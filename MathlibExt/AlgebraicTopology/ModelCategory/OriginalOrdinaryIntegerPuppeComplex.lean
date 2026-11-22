/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryIntegerPuppeExactSequence
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Lean.Elab.Tactic.Omega

/-!
# The whole original integer Puppe complex

Every original integer labels its fibre, input source and target groups.
The actual first leg, input and original connecting homomorphism form one
unbounded complex. The only domain transport is the literal integer
identity (n - 1) + 1 = n; it does not replace the connecting map.

The original ordinary suspension equivalence remains an explicit input.
The original generation datum, Q/R/J choices and caller fibre cocone are
retained. No stable model or arbitrary coordinate-T inversion is inferred.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopicalAlgebra.OriginalOrdinaryIntegerPuppeComplex

/-- Every original integer keeps its three specified positions in the same unbounded sequence. -/
inductive Position
  | fibre (n : ℤ)
  | source (n : ℤ)
  | target (n : ℤ)
  deriving DecidableEq

/-- The original boundary keeps its literal integer predecessor after the original input. -/
def nextPosition : Position → Position
  | .fibre n => .source n
  | .source n => .target n
  | .target n => .fibre (n - 1)

/-- The incoming original boundary retains the literal integer successor. -/
def previousPosition : Position → Position
  | .fibre n => .target (n + 1)
  | .source n => .fibre n
  | .target n => .source n

/-- Every incoming original position is followed by that same specified original position. -/
theorem next_previous (i : Position) : nextPosition (previousPosition i) = i := by
  cases i <;> simp only [nextPosition, previousPosition, add_sub_cancel_right]

/-- Every outgoing original position has that same original incoming position. -/
theorem previous_next (i : Position) : previousPosition (nextPosition i) = i := by
  cases i <;> simp only [nextPosition, previousPosition, sub_add_cancel]

/-- No original degree or position is merged by the full original next-position action. -/
theorem next_injective : Function.Injective nextPosition := by
  intro i j h
  have h' := congrArg previousPosition h
  simpa only [previous_next] using h'

/-- The three original positions have their actual consecutive integer chain degrees. -/
def degree : Position → ℤ
  | .fibre n => 3 * n + 2
  | .source n => 3 * n + 1
  | .target n => 3 * n

/-- The literal next original Puppe position decreases the actual chain degree by one. -/
theorem degree_next (i : Position) : degree (nextPosition i) + 1 = degree i := by
  cases i <;> simp only [degree, nextPosition] <;> omega

/-- The actual integer degree retains the entire original integer and its specified position. -/
theorem degree_injective : Function.Injective degree := by
  intro i j h
  cases i with
  | fibre n =>
    cases j with
    | fibre m => congr 1; change 3 * n + 2 = 3 * m + 2 at h; omega
    | source m => change 3 * n + 2 = 3 * m + 1 at h; omega
    | target m => change 3 * n + 2 = 3 * m at h; omega
  | source n =>
    cases j with
    | fibre m => change 3 * n + 1 = 3 * m + 2 at h; omega
    | source m => congr 1; change 3 * n + 1 = 3 * m + 1 at h; omega
    | target m => change 3 * n + 1 = 3 * m at h; omega
  | target n =>
    cases j with
    | fibre m => change 3 * n = 3 * m + 2 at h; omega
    | source m => change 3 * n = 3 * m + 1 at h; omega
    | target m => congr 1; change 3 * n = 3 * m at h; omega

/-- Every actual integer chain degree keeps exactly one original integer and one of its three specified positions. -/
theorem degree_surjective : Function.Surjective degree := by
  intro k
  have h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h with h | h | h
  · refine ⟨.target (k / 3), ?_⟩
    change 3 * (k / 3) = k
    omega
  · refine ⟨.source (k / 3), ?_⟩
    change 3 * (k / 3) + 1 = k
    omega
  · refine ⟨.fibre (k / 3), ?_⟩
    change 3 * (k / 3) + 2 = k
    omega

/-- The literal full original integer/position dictionary is an equivalence with all integer chain degrees. -/
def degreeEquiv : Position ≃ ℤ := Equiv.ofBijective degree ⟨degree_injective, degree_surjective⟩

/-- The original long-complex shape keeps only the actual next original position. -/
@[implicit_reducible]
def shape : ComplexShape Position where
  Rel i j := nextPosition i = j
  next_eq h h' := h.symm.trans h'
  prev_eq h h' := next_injective (h.trans h'.symm)

/-- The entire original shape relation is exactly the actual integer down-complex relation. -/
theorem shape_degree_iff (i j : Position) : shape.Rel i j ↔ degree j + 1 = degree i := by
  constructor
  · intro h
    rw [← h]
    exact degree_next i
  · intro h
    apply degree_injective
    have hn := degree_next i
    omega

/-- The actual outgoing index of the whole complex is the original next position. -/
theorem shape_next (i : Position) : shape.next i = nextPosition i := shape.next_eq' rfl

/-- The actual incoming index of the whole complex is the original previous position. -/
theorem shape_previous (i : Position) : shape.prev i = previousPosition i :=
  shape.prev_eq' (next_previous i)


private theorem precompose_equal_zero {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {A B E : D} (a : A ⟶ B) (b : B ⟶ E) (hb : b = 0) : a ≫ b = 0 := by
  rw [hb]
  exact CategoryTheory.Limits.comp_zero

private theorem relabeledStep {D : Type*} [Category* D]
    (A B : ℤ → D) (b : ∀ k, A (k + 1) ⟶ B k) (m n : ℤ) (h : m = n) :
    (eqToHom (congrArg (fun k => A (k + 1)) h.symm) ≫ b m) ≫
      eqToHom (congrArg B h) = b n := by
  subst m
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]
  (Z : C) (hZ : IsZero Z) {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

/-- Every original position retains its whole original contravariant Hom-group functor. -/
@[implicit_reducible]
def groups (i : Position) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (HomotopyCategory C)ᵒᵖ ⥤ Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  cases i with
  | fibre n => exact OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplexFunctor g Z hZ f s hs n ⋙
    ShortComplex.π₁
  | source n => exact OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplexFunctor g Z hZ f s hs n ⋙
    ShortComplex.π₂
  | target n => exact OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplexFunctor g Z hZ f s hs n ⋙
    ShortComplex.π₃


/-- The original input source projection is the same full source-group functor at its literal successor degree. -/
private theorem inputFirst_eq (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OriginalOrdinaryIntegerPuppeExactSequence.inputShortComplexFunctor g Z hZ f s hs n ⋙ ShortComplex.π₁ =
      groups g Z hZ f s hs (.source (n + 1)) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rfl

/-- The original input middle projection is the same full target-group functor at its literal successor degree. -/
private theorem inputSecond_eq (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OriginalOrdinaryIntegerPuppeExactSequence.inputShortComplexFunctor g Z hZ f s hs n ⋙ ShortComplex.π₂ =
      groups g Z hZ f s hs (.target (n + 1)) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rfl

/-- The original input output projection is the same full fibre-group functor at its literal degree. -/
private theorem inputThird_eq (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OriginalOrdinaryIntegerPuppeExactSequence.inputShortComplexFunctor g Z hZ f s hs n ⋙ ShortComplex.π₃ =
      groups g Z hZ f s hs (.fibre n) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rfl


/-- The actual original boundary at n acts on the same full coefficient functors at degrees n+1 and n. -/
def boundaryNextStep (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    groups g Z hZ f s hs (.target (n + 1)) ⟶ groups g Z hZ f s hs (.fibre n) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact eqToHom (inputSecond_eq g Z hZ f s hs n).symm ≫
    Functor.whiskerLeft
      (OriginalOrdinaryIntegerPuppeExactSequence.inputShortComplexFunctor g Z hZ f s hs n)
      ShortComplex.π₂Toπ₃ ≫ eqToHom (inputThird_eq g Z hZ f s hs n)

/-- The integer predecessor acts by the literal equality of the whole target-group functor before the original boundary.
-/
def boundaryStep (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    groups g Z hZ f s hs (.target n) ⟶ groups g Z hZ f s hs (.fibre (n - 1)) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact eqToHom (congrArg (fun k => groups g Z hZ f s hs (.target k))
    (sub_add_cancel n 1).symm) ≫ boundaryNextStep g Z hZ f s hs (n - 1)

/-- Every original boundary component is the evaluation of that same full natural coefficient boundary. -/
def boundaryComponent (n : ℤ) (T : (HomotopyCategory C)ᵒᵖ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (groups g Z hZ f s hs (.target n)).obj T ⟶
      (groups g Z hZ f s hs (.fibre (n - 1))).obj T :=
  (boundaryStep g Z hZ f s hs n).app T

/-- Every entire original differential is the same original first leg, input, or transported original boundary. -/
def step (i : Position) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    groups g Z hZ f s hs i ⟶ groups g Z hZ f s hs (nextPosition i) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  cases i with
  | fibre n =>
    exact Functor.whiskerLeft (OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplexFunctor g Z hZ f s hs n)
      ShortComplex.π₁Toπ₂
  | source n =>
    exact Functor.whiskerLeft (OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplexFunctor g Z hZ f s hs n)
      ShortComplex.π₂Toπ₃
  | target n => exact boundaryStep g Z hZ f s hs n



/-- The literal original boundary and first leg retain their actual full natural zero composite. -/
theorem boundaryNextStep_first_zero (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    boundaryNextStep g Z hZ f s hs n ≫ step g Z hZ f s hs (.fibre n) = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply NatTrans.ext
  funext T
  change ((𝟙 _ ≫ AddCommGrpCat.ofHom
      (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T.unop) ≫ 𝟙 _) ≫
    AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.firstLeg g Z hZ f s n T.unop)) = 0
  simp only [Category.id_comp, Category.comp_id]
  apply AddCommGrpCat.hom_ext
  exact OriginalOrdinaryIntegerPuppeExactSequence.boundary_first_zero g Z hZ f s hs n T.unop

/-- The same original input and boundary retain their actual zero composite before any integer-label transport. -/
theorem input_boundaryNextStep_zero (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    step g Z hZ f s hs (.source (n + 1)) ≫ boundaryNextStep g Z hZ f s hs n = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply NatTrans.ext
  funext T
  change AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.input g f (n + 1) T.unop) ≫
    (𝟙 _ ≫ AddCommGrpCat.ofHom
      (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T.unop) ≫ 𝟙 _) = 0
  simp only [Category.id_comp, Category.comp_id]
  apply AddCommGrpCat.hom_ext
  exact OriginalOrdinaryIntegerPuppeExactSequence.input_boundary_zero g Z hZ f s hs n T.unop

/-- Every literal integer equality preserves both whole group endpoints and the SAME actual input transformation. -/
theorem input_transport (m n : ℤ) (h : m = n) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    step g Z hZ f s hs (.source n) ≫
        eqToHom (congrArg (fun k => groups g Z hZ f s hs (.target k)) h.symm) =
      eqToHom (congrArg (fun k => groups g Z hZ f s hs (.source k)) h.symm) ≫
        step g Z hZ f s hs (.source m) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  subst n
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Both consecutive original differentials have zero composite with the full actual integer-label transports retained.
-/
theorem step_comp_step (i : Position) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    step g Z hZ f s hs i ≫ step g Z hZ f s hs (nextPosition i) = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  cases i with
  | fibre n =>
    apply NatTrans.ext
    funext T
    change AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.firstLeg g Z hZ f s n T.unop) ≫
      AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.input g f n T.unop) = 0
    apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppeExactSequence.first_input_zero g Z hZ f s hs n T.unop
  | source n =>
    change step g Z hZ f s hs (.source n) ≫ boundaryStep g Z hZ f s hs n = 0
    have ht := input_transport g Z hZ f s hs ((n - 1) + 1) n (sub_add_cancel n 1)
    have hz := input_boundaryNextStep_zero g Z hZ f s hs (n - 1)
    change step g Z hZ f s hs (.source n) ≫
      (eqToHom (congrArg (fun k => groups g Z hZ f s hs (.target k)) (sub_add_cancel n 1).symm) ≫
        boundaryNextStep g Z hZ f s hs (n - 1)) = 0
    calc
      step g Z hZ f s hs (.source n) ≫
          (eqToHom (congrArg (fun k => groups g Z hZ f s hs (.target k)) (sub_add_cancel n 1).symm) ≫
            boundaryNextStep g Z hZ f s hs (n - 1)) =
        (step g Z hZ f s hs (.source n) ≫
          eqToHom (congrArg (fun k => groups g Z hZ f s hs (.target k)) (sub_add_cancel n 1).symm)) ≫
            boundaryNextStep g Z hZ f s hs (n - 1) := (Category.assoc _ _ _).symm
      _ = (eqToHom (congrArg (fun k => groups g Z hZ f s hs (.source k)) (sub_add_cancel n 1).symm) ≫
          step g Z hZ f s hs (.source ((n - 1) + 1))) ≫ boundaryNextStep g Z hZ f s hs (n - 1) :=
        congrArg (fun q => q ≫ boundaryNextStep g Z hZ f s hs (n - 1)) ht
      _ = eqToHom (congrArg (fun k => groups g Z hZ f s hs (.source k)) (sub_add_cancel n 1).symm) ≫
          (step g Z hZ f s hs (.source ((n - 1) + 1)) ≫ boundaryNextStep g Z hZ f s hs (n - 1)) :=
        Category.assoc _ _ _
      _ = 0 := precompose_equal_zero
        (D := (HomotopyCategory C)ᵒᵖ ⥤ Ab)
        (A := groups g Z hZ f s hs (.source n))
        (B := groups g Z hZ f s hs (.source ((n - 1) + 1)))
        (E := groups g Z hZ f s hs (.fibre (n - 1)))
        (eqToHom (congrArg (fun k => groups g Z hZ f s hs (.source k)) (sub_add_cancel n 1).symm))
        (step g Z hZ f s hs (.source ((n - 1) + 1)) ≫ boundaryNextStep g Z hZ f s hs (n - 1)) hz
  | target n =>
    change boundaryStep g Z hZ f s hs n ≫ step g Z hZ f s hs (.fibre (n - 1)) = 0
    have hz := boundaryNextStep_first_zero g Z hZ f s hs (n - 1)
    let ct : groups g Z hZ f s hs (.target n) ⟶ groups g Z hZ f s hs (.target ((n - 1) + 1)) := eqToHom (congrArg (fun k
      => groups g Z hZ f s hs (.target k)) (sub_add_cancel n 1).symm)
    change (ct ≫ boundaryNextStep g Z hZ f s hs (n - 1)) ≫ step g Z hZ f s hs (.fibre (n - 1)) = 0
    calc
      (ct ≫ boundaryNextStep g Z hZ f s hs (n - 1)) ≫ step g Z hZ f s hs (.fibre (n - 1)) =
          ct ≫ (boundaryNextStep g Z hZ f s hs (n - 1) ≫ step g Z hZ f s hs (.fibre (n - 1))) :=
        Category.assoc _ _ _
      _ = ct ≫ (0 : groups g Z hZ f s hs (.target ((n - 1) + 1)) ⟶
          groups g Z hZ f s hs (.source (n - 1))) :=
        congrArg (fun q : groups g Z hZ f s hs (.target ((n - 1) + 1)) ⟶
          groups g Z hZ f s hs (.source (n - 1)) => ct ≫ q) hz
      _ = 0 := by
        apply NatTrans.ext
        funext T
        exact CategoryTheory.Limits.comp_zero (C := Ab) (f := ct.app T)
          (Z := (groups g Z hZ f s hs (.source (n - 1))).obj T)

/-- The whole actual original integer Puppe sequence is one complex of its full coefficient functors. -/
@[implicit_reducible]
def complex :
    letI := OrdinaryStableHoPreadditive.preadditive g
    HomologicalComplex ((HomotopyCategory C)ᵒᵖ ⥤ Ab) shape := by
  let := OrdinaryStableHoPreadditive.preadditive g
  classical
  refine
    { X := groups g Z hZ f s hs
      d := fun i j => if h : nextPosition i = j then
        step g Z hZ f s hs i ≫ eqToHom (congrArg (groups g Z hZ f s hs) h) else 0
      shape := ?_
      d_comp_d' := ?_ }
  · intro i j h
    exact dite_eq_right h
  · intro i j k hij hjk
    change nextPosition i = j at hij
    change nextPosition j = k at hjk
    subst j
    subst k
    simp only [eqToHom_refl, Category.comp_id]
    exact step_comp_step g Z hZ f s hs i


/-- Every original Ho coefficient evaluates the SAME whole natural integer Puppe complex. -/
@[implicit_reducible]
def coefficientComplex (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    HomologicalComplex Ab shape := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (((evaluation (HomotopyCategory C)ᵒᵖ Ab).obj (op T)).mapHomologicalComplex shape).obj
    (complex g Z hZ f s hs)

/-- Every full original Ho coefficient map acts on the whole complex by the same original Hom-group maps. -/
def coefficientFunctor :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (HomotopyCategory C)ᵒᵖ ⥤ HomologicalComplex Ab shape := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (complex g Z hZ f s hs).asFunctor

/-- Every original outgoing complex differential is the evaluation of its SAME original full natural step. -/
theorem coefficientComplex_d_next (T : HomotopyCategory C) (i : Position) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).d i (nextPosition i) =
      (step g Z hZ f s hs i).app (op T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  change ((if h : nextPosition i = nextPosition i then
    step g Z hZ f s hs i ≫ eqToHom (congrArg (groups g Z hZ f s hs) h) else 0).app (op T)) = _
  simp only [eqToHom_refl, Category.comp_id, dite_true]

/-- At its literal original integer endpoints, the natural boundary component is the original connecting homomorphism.
-/
theorem boundaryNextStep_app (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (boundaryNextStep g Z hZ f s hs n).app (op T) =
      AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  have he₁ : (eqToHom (inputSecond_eq g Z hZ f s hs n).symm).app (op T) = 𝟙 _ := rfl
  have he₃ : (eqToHom (inputThird_eq g Z hZ f s hs n)).app (op T) = 𝟙 _ := rfl
  simp only [boundaryNextStep, NatTrans.comp_app]
  rw [he₁, he₃, Category.id_comp, Category.comp_id]
  rfl

/-- The full fibre/input slice is isomorphic to the original exact abelian short complex at the SAME integer and
coefficient. -/
def fibreSliceIso (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).sc' (.fibre n) (.source n) (.target n) ≅
      OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplex g Z hZ f s hs n T := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (coefficientComplex_d_next g Z hZ f s hs T (.fibre n)).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (coefficientComplex_d_next g Z hZ f s hs T (.source n)).symm

/-- The whole original complex is exact at every original source position, using its SAME actual first leg and input. -/
theorem source_exactAt (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).ExactAt (.source n) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply ((coefficientComplex g Z hZ f s hs T).exactAt_iff' (.fibre n) (.source n) (.target n)
    (by rw [shape_previous]; rfl) (by rw [shape_next]; rfl)).mpr
  exact ShortComplex.exact_of_iso (fibreSliceIso g Z hZ f s hs n T).symm
    (OriginalOrdinaryIntegerPuppeExactSequence.fibreShortComplex_exact g Z hZ f s hs n T)


/-- At a literal integer successor the full complex differential is the SAME original connecting homomorphism. -/
theorem complex_d_boundary_successor (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (complex g Z hZ f s hs).d (.target (n + 1)) (.fibre n) =
      boundaryNextStep g Z hZ f s hs n := by
  let := OrdinaryStableHoPreadditive.preadditive g
  classical
  have hn : (n + 1) - 1 = n := by omega
  have hp : nextPosition (.target (n + 1)) = .fibre n := congrArg Position.fibre hn
  change (if h : nextPosition (.target (n + 1)) = .fibre n then
    step g Z hZ f s hs (.target (n + 1)) ≫
      eqToHom (congrArg (groups g Z hZ f s hs) h) else 0) = _
  rw [dite_eq_left hp]
  exact relabeledStep
    (fun k => groups g Z hZ f s hs (.target k))
    (fun k => groups g Z hZ f s hs (.fibre k))
    (boundaryNextStep g Z hZ f s hs) ((n + 1) - 1) n hn

/-- Each coefficient evaluates that SAME complete natural connecting map at the literal successor degree. -/
theorem coefficientComplex_d_boundary_successor (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).d (.target (n + 1)) (.fibre n) =
      AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (NatTrans.congr_app (complex_d_boundary_successor g Z hZ f s hs n) (op T)).trans
    (boundaryNextStep_app g Z hZ f s hs n T)

/-- The actual boundary/fibre slice keeps the full original connecting map and its integer source isomorphism. -/
def boundarySliceIso (p : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OriginalOrdinaryIntegerPuppeExactSequence.boundaryShortComplex g Z hZ f s hs (p - 1) T ≅
      (coefficientComplex g Z hZ f s hs T).sc' (.target p) (.fibre (p - 1)) (.source (p - 1)) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  generalize hn : p - 1 = n at ⊢
  have hp : p = n + 1 := by omega
  subst p
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact coefficientComplex_d_boundary_successor g Z hZ f s hs n T
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact coefficientComplex_d_next g Z hZ f s hs T (.fibre n)

/-- The actual input/boundary slice keeps BOTH original integer group endpoints and every full original input map. -/
def inputSliceIso (p : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OriginalOrdinaryIntegerPuppeExactSequence.inputShortComplex g Z hZ f s hs (p - 1) T ≅
      (coefficientComplex g Z hZ f s hs T).sc' (.source p) (.target p) (.fibre (p - 1)) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  generalize hn : p - 1 = n at ⊢
  have hp : p = n + 1 := by omega
  subst p
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact coefficientComplex_d_next g Z hZ f s hs T (.source (n + 1))
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact coefficientComplex_d_boundary_successor g Z hZ f s hs n T

/-- Every original boundary/fibre position is exact, with the original integer source isomorphism retained. -/
theorem fibre_predecessor_exactAt (p : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).ExactAt (.fibre (p - 1)) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply ((coefficientComplex g Z hZ f s hs T).exactAt_iff'
    (.target p) (.fibre (p - 1)) (.source (p - 1))
    (by simp only [shape_previous, previousPosition, sub_add_cancel])
    (by rw [shape_next]; rfl)).mpr
  exact ShortComplex.exact_of_iso (boundarySliceIso g Z hZ f s hs p T)
    (OriginalOrdinaryIntegerPuppeExactSequence.boundaryShortComplex_exact g Z hZ f s hs (p - 1) T)

/-- Every original full input/boundary position is exact through BOTH original integer group isomorphisms. -/
theorem target_exactAt (p : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).ExactAt (.target p) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply ((coefficientComplex g Z hZ f s hs T).exactAt_iff'
    (.source p) (.target p) (.fibre (p - 1))
    (by rw [shape_previous]; rfl) (by rw [shape_next]; rfl)).mpr
  exact ShortComplex.exact_of_iso (inputSliceIso g Z hZ f s hs p T)
    (OriginalOrdinaryIntegerPuppeExactSequence.inputShortComplex_exact g Z hZ f s hs (p - 1) T)

/-- The entire original integer Puppe complex is acyclic at EVERY original position for EVERY full Ho coefficient. -/
theorem coefficientComplex_acyclic (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (coefficientComplex g Z hZ f s hs T).Acyclic := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro i
  cases i with
  | fibre n =>
    have h := fibre_predecessor_exactAt g Z hZ f s hs (n + 1) T
    have hn : (n + 1) - 1 = n := by omega
    simpa only [hn] using h
  | source n => exact source_exactAt g Z hZ f s hs n T
  | target n => exact target_exactAt g Z hZ f s hs n T

/-- Homology of the SAME full complex vanishes at all original integer positions and every original Ho coefficient. -/
theorem coefficientComplex_homology_zero (T : HomotopyCategory C) (i : Position) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    IsZero ((coefficientComplex g Z hZ f s hs T).homology i) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (coefficientComplex_acyclic g Z hZ f s hs T i).isZero_homology

end HomotopicalAlgebra.OriginalOrdinaryIntegerPuppeComplex
