/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryIntegerPuppePositions
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoFiberGroupExactness
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryCovariantPuppeThirdPosition
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The complete original integer covariant Puppe exact sequence

The third ordinary loop-image theorem is transported by the actual
integer successor and the same additive ordinary suspension-loop
adjunction. The original connecting function is retained; it is not
replaced by a map with a supplied exactness property.

At every integer, all three adjacent positions of the sequence are exact.
They are also actual short complexes of abelian groups, with zero homology.
Every full Ho coefficient map acts on the whole sequence by the original
integer source-shift maps. The three resulting short-complex functors retain
all specified coefficient labels.

The ordinary suspension-equivalence hypothesis is explicit. No stable
model or equivalence for an arbitrary spectra coordinate T is inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopicalAlgebra.OriginalOrdinaryIntegerPuppeExactSequence

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "Ω" => DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)
local notation "hom" => OriginalOrdinaryIntegerPuppePositions.hom g
local notation "θ" => OriginalOrdinaryIntegerPuppePositions.successorHomEquiv g

variable (Z : C) (hZ : IsZero Z) {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

local notation "F" => OriginalOrdinaryHoFibrationFiberKernel.fiber g Z hZ f s
local notation "δ" => OriginalOrdinaryHoPuppeConnection.connecting g Z hZ f s hs
local notation "N" => OriginalOrdinaryHoFibrationFiberKernel.null g Z hZ
local notation "b" => OriginalOrdinaryIntegerPuppePositions.boundary g Z hZ f s hs
local notation "a" => OriginalOrdinaryIntegerPuppePositions.firstLeg g Z hZ f s
local notation "q" => OriginalOrdinaryIntegerPuppePositions.input g f

private theorem null_zero (T E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    N T E = 0 :=
  OriginalOrdinaryHoFiberGroupExactness.null_eq_zero g Z hZ T E

/-- The actual successor comparison transports the complete input-image to the loop-image with both target functions. -/
theorem successor_input_image_iff (n : ℤ) (T : HomotopyCategory C) (h : hom (n + 1) T Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ k : hom (n + 1) T X, k ≫ f = h) ↔
      ∃ k : hom n T ((Ω).obj X), k ≫ (Ω).map f = θ n T Y h := by
  let := OrdinaryStableHoPreadditive.preadditive g
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨θ n T X k, ?_⟩
    rw [← OriginalOrdinaryIntegerPuppePositions.successorHomEquiv_target, hk]
  · rintro ⟨k, hk⟩
    refine ⟨(θ n T X).symm k, ?_⟩
    apply (θ n T Y).injective
    rw [OriginalOrdinaryIntegerPuppePositions.successorHomEquiv_target,
      AddEquiv.apply_symm_apply, hk]

/-- The input/boundary position is exact at EVERY integer source degree of the SAME original full Ho arrow and fibre. -/
theorem input_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (q (n + 1) T) (b n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro h
  change θ n T Y h ≫ δ = 0 ↔ ∃ k : hom (n + 1) T X, k ≫ f = h
  rw [← null_zero g Z hZ ((OrdinaryStableIntegerHom.shift g n).obj T) F]
  exact ((successor_input_image_iff g f n T h).trans
    (OriginalOrdinaryCovariantPuppeThirdPosition.loop_image_iff g Z hZ f s hs
      ((OrdinaryStableIntegerHom.shift g n).obj T) (θ n T Y h))).symm

/-- All three group positions are exact at every integer, using the same actual original boundary, first leg and input.
-/
theorem integer_long_exact (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ∀ n : ℤ, Function.Exact (b n T) (a n T) ∧
      Function.Exact (a n T) (q n T) ∧ Function.Exact (q (n + 1) T) (b n T) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro n
  exact ⟨OriginalOrdinaryIntegerPuppePositions.boundary_exact g Z hZ f s hs n T,
    OriginalOrdinaryIntegerPuppePositions.fibre_exact g Z hZ f s hs n T,
    input_exact g Z hZ f s hs n T⟩

/-- The boundary and the same original first leg have zero composite at every integer source degree. -/
theorem boundary_first_zero (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (a n T).comp (b n T) = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (OriginalOrdinaryIntegerPuppePositions.boundary_exact g Z hZ f s hs n T).addMonoidHom_comp_eq_zero

include hs in
/-- The first leg and the SAME full original input map have zero composite at every integer source degree. -/
theorem first_input_zero (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (q n T).comp (a n T) = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (OriginalOrdinaryIntegerPuppePositions.fibre_exact g Z hZ f s hs n T).addMonoidHom_comp_eq_zero

/-- The SAME full original input and boundary have zero composite across each original integer successor. -/
theorem input_boundary_zero (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (b n T).comp (q (n + 1) T) = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (input_exact g Z hZ f s hs n T).addMonoidHom_comp_eq_zero

/-- The actual boundary/fibre position is a short complex of the original abelian Hom groups. -/
def boundaryShortComplex (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ShortComplex Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine ShortComplex.mk (AddCommGrpCat.ofHom (b n T)) (AddCommGrpCat.ofHom (a n T)) ?_
  apply AddCommGrpCat.hom_ext
  exact boundary_first_zero g Z hZ f s hs n T

/-- The actual fibre/input position is a short complex of the SAME original abelian Hom groups. -/
def fibreShortComplex (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ShortComplex Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine ShortComplex.mk (AddCommGrpCat.ofHom (a n T)) (AddCommGrpCat.ofHom (q n T)) ?_
  apply AddCommGrpCat.hom_ext
  exact first_input_zero g Z hZ f s hs n T

/-- The new input/boundary position is a short complex across the SAME original integer successor. -/
def inputShortComplex (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ShortComplex Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine ShortComplex.mk (AddCommGrpCat.ofHom (q (n + 1) T)) (AddCommGrpCat.ofHom (b n T)) ?_
  apply AddCommGrpCat.hom_ext
  exact input_boundary_zero g Z hZ f s hs n T

/-- Every actual boundary/fibre short complex is categorically exact. -/
theorem boundaryShortComplex_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (boundaryShortComplex g Z hZ f s hs n T).Exact := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  exact OriginalOrdinaryIntegerPuppePositions.boundary_exact g Z hZ f s hs n T

/-- Every actual fibre/input short complex is categorically exact. -/
theorem fibreShortComplex_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (fibreShortComplex g Z hZ f s hs n T).Exact := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  exact OriginalOrdinaryIntegerPuppePositions.fibre_exact g Z hZ f s hs n T

/-- Every actual input/boundary short complex is categorically exact at the SAME original integer successor. -/
theorem inputShortComplex_exact (n : ℤ) (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (inputShortComplex g Z hZ f s hs n T).Exact := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  exact input_exact g Z hZ f s hs n T

/-- Homology vanishes at all three actual original integer positions, at every integer and every full Ho coefficient. -/
theorem integer_homology_zero (T : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ∀ n : ℤ,
      IsZero (boundaryShortComplex g Z hZ f s hs n T).homology ∧
      IsZero (fibreShortComplex g Z hZ f s hs n T).homology ∧
      IsZero (inputShortComplex g Z hZ f s hs n T).homology := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro n
  exact ⟨(ShortComplex.exact_iff_isZero_homology _).mp (boundaryShortComplex_exact g Z hZ f s hs n T),
    (ShortComplex.exact_iff_isZero_homology _).mp (fibreShortComplex_exact g Z hZ f s hs n T),
    (ShortComplex.exact_iff_isZero_homology _).mp (inputShortComplex_exact g Z hZ f s hs n T)⟩

private theorem coefficientAb_id (n : ℤ) (T E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n (𝟙 T) E) = 𝟙 _ := by
  let := OrdinaryStableHoPreadditive.preadditive g
  ext h
  change (OrdinaryStableIntegerHom.shift g n).map (𝟙 T) ≫ h = h
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem coefficientAb_comp (n : ℤ) {T T' T'' : HomotopyCategory C}
    (c : T' ⟶ T) (c' : T'' ⟶ T') (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n (c' ≫ c) E) =
      AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c E) ≫
        AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c' E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  ext h
  change (OrdinaryStableIntegerHom.shift g n).map (c' ≫ c) ≫ h =
    (OrdinaryStableIntegerHom.shift g n).map c' ≫ ((OrdinaryStableIntegerHom.shift g n).map c ≫ h)
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Every full coefficient map acts on the actual boundary/fibre short complex, retaining both original naturality
squares. -/
def boundaryShortComplexMap (n : ℤ) {T T' : HomotopyCategory C} (c : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    boundaryShortComplex g Z hZ f s hs n T ⟶ boundaryShortComplex g Z hZ f s hs n T' := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine
    { τ₁ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g (n + 1) c Y)
      τ₂ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c F)
      τ₃ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c X)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppePositions.boundary_naturality g Z hZ f s hs n c
  · apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppePositions.firstLeg_naturality g Z hZ f s n c

/-- Every full coefficient map acts on the actual fibre/input short complex, keeping the SAME original input square. -/
def fibreShortComplexMap (n : ℤ) {T T' : HomotopyCategory C} (c : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    fibreShortComplex g Z hZ f s hs n T ⟶ fibreShortComplex g Z hZ f s hs n T' := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine
    { τ₁ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c F)
      τ₂ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c X)
      τ₃ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c Y)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppePositions.firstLeg_naturality g Z hZ f s n c
  · apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppePositions.input_naturality g f n c

/-- Every full coefficient map acts on the actual input/boundary short complex across its original successor. -/
def inputShortComplexMap (n : ℤ) {T T' : HomotopyCategory C} (c : T' ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    inputShortComplex g Z hZ f s hs n T ⟶ inputShortComplex g Z hZ f s hs n T' := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine
    { τ₁ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g (n + 1) c X)
      τ₂ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g (n + 1) c Y)
      τ₃ := AddCommGrpCat.ofHom (OriginalOrdinaryIntegerPuppePositions.coefficientMap g n c F)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppePositions.input_naturality g f (n + 1) c
  · apply AddCommGrpCat.hom_ext
    exact OriginalOrdinaryIntegerPuppePositions.boundary_naturality g Z hZ f s hs n c

/-- The whole boundary/fibre position is contravariantly functorial in every original Ho coefficient. -/
def boundaryShortComplexFunctor (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (HomotopyCategory C)ᵒᵖ ⥤ ShortComplex Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine
    { obj := fun T => boundaryShortComplex g Z hZ f s hs n T.unop
      map := fun c => boundaryShortComplexMap g Z hZ f s hs n c.unop
      map_id := ?_
      map_comp := ?_ }
  · intro T
    apply ShortComplex.hom_ext
    · exact coefficientAb_id g (n + 1) T.unop Y
    · exact coefficientAb_id g n T.unop F
    · exact coefficientAb_id g n T.unop X
  · intro T T' T'' c c'
    apply ShortComplex.hom_ext
    · exact coefficientAb_comp g (n + 1) c.unop c'.unop Y
    · exact coefficientAb_comp g n c.unop c'.unop F
    · exact coefficientAb_comp g n c.unop c'.unop X

/-- The whole fibre/input position is contravariantly functorial in the SAME original Ho coefficients. -/
def fibreShortComplexFunctor (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (HomotopyCategory C)ᵒᵖ ⥤ ShortComplex Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine
    { obj := fun T => fibreShortComplex g Z hZ f s hs n T.unop
      map := fun c => fibreShortComplexMap g Z hZ f s hs n c.unop
      map_id := ?_
      map_comp := ?_ }
  · intro T
    apply ShortComplex.hom_ext
    · exact coefficientAb_id g n T.unop F
    · exact coefficientAb_id g n T.unop X
    · exact coefficientAb_id g n T.unop Y
  · intro T T' T'' c c'
    apply ShortComplex.hom_ext
    · exact coefficientAb_comp g n c.unop c'.unop F
    · exact coefficientAb_comp g n c.unop c'.unop X
    · exact coefficientAb_comp g n c.unop c'.unop Y

/-- The whole input/boundary position is contravariantly functorial across the SAME original integer successor. -/
def inputShortComplexFunctor (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (HomotopyCategory C)ᵒᵖ ⥤ ShortComplex Ab := by
  let := OrdinaryStableHoPreadditive.preadditive g
  refine
    { obj := fun T => inputShortComplex g Z hZ f s hs n T.unop
      map := fun c => inputShortComplexMap g Z hZ f s hs n c.unop
      map_id := ?_
      map_comp := ?_ }
  · intro T
    apply ShortComplex.hom_ext
    · exact coefficientAb_id g (n + 1) T.unop X
    · exact coefficientAb_id g (n + 1) T.unop Y
    · exact coefficientAb_id g n T.unop F
  · intro T T' T'' c c'
    apply ShortComplex.hom_ext
    · exact coefficientAb_comp g (n + 1) c.unop c'.unop X
    · exact coefficientAb_comp g (n + 1) c.unop c'.unop Y
    · exact coefficientAb_comp g n c.unop c'.unop F

/-- ALL supplied original coefficient labels and ALL integer degrees retain the complete actual three-position exact
sequence. -/
theorem generator_integer_long_exact {I : Type*} (G : I → HomotopyCategory C) (k : I) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ∀ n : ℤ, Function.Exact (b n (G k)) (a n (G k)) ∧
      Function.Exact (a n (G k)) (q n (G k)) ∧ Function.Exact (q (n + 1) (G k)) (b n (G k)) :=
  integer_long_exact g Z hZ f s hs (G k)

end HomotopicalAlgebra.OriginalOrdinaryIntegerPuppeExactSequence
