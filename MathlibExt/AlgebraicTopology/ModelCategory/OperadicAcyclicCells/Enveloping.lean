/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells
public import MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingAttachmentFiltration
public import MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingOrbitCells
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Full original operadic acyclic attachments

The actual colored operadic free-algebra pushout retains both original legs,
all caller cofans, its source and endpoint, and its native evaluated cell
history. The two conventional source alternatives imply couniversal weakness
of the same original old leg. The actual nil stage keeps its original carrier
isomorphism. All results preserve the original coefficient and color universes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w wO ν wG uc ui us uj vj v u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open CategoryTheory.SmallObject.CellularNormalization
open CategoryTheory.OperadicOrbitCells
open HomotopicalAlgebra.OperadicAcyclicCells

namespace HomotopicalAlgebra.OperadicAcyclicCells.Complexes

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] [UnivLE.{wO, w}] [UnivLE.{ν, w}]
  {O : Type wO} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}

omit [UnivLE.{wO, w}] [UnivLE.{ν, w}] in
/-- A full actual native relative complex has the same original whole
arrow in the stated cellular class, with independent ordinal and cofan labels. -/
theorem originalComplex_cellularMembership
    (c : RelativeCellComplex.{ν}
      (fun _ : O => (orbitGenerators (trivialCofibrations C)).homFamily) f) :
    cellularClosure.{wO, ν} (orbitGenerators (trivialCofibrations C)) f := by
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions
    (coproducts.{ν} (orbitGenerators (trivialCofibrations C))).pushouts O f
  simpa only [ofHoms_homFamily] using
    (c.transfiniteCompositionOfShape (orbitGenerators (trivialCofibrations C)).homFamily).mem

/-- The first alternative acts on every original cell occurrence and
the original endpoint, with no properness or generating-source input. -/
theorem originalComplex_weak_transfinite
    [(weakEquivalences C).IsStableUnderTransfiniteComposition.{w}]
    (h : AcyclicSymmetricHMonoidality C)
    (c : RelativeCellComplex.{ν}
      (fun _ : O => (orbitGenerators (trivialCofibrations C)).homFamily) f) :
    couniversalWeakEquivalences C f :=
  operadic_acyclic_cells_of_weak_transfinite.{w, wO, ν} h f
    (originalComplex_cellularMembership.{w, wO, ν} c)

variable [HasLimitsOfSize.{w, w} C] [IsLeftProper C]
  {κ : Cardinal.{wG}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The second alternative uses the caller's original I/J generating
record and its actual compact I endpoints; the complete native complex is retained. -/
theorem originalComplex_strong_admissible
    (d : CofibrantGenerationData C κ)
    (hStrong : StrongAdmissibleGeneration.{w, ν} C d.I)
    (h : AcyclicSymmetricHMonoidalityOrdinary C)
    (c : RelativeCellComplex.{ν}
      (fun _ : O => (orbitGenerators (trivialCofibrations C)).homFamily) f) :
    couniversalWeakEquivalences C f :=
  operadic_acyclic_cells_of_strong_admissible.{w, wO, ν} d.I d.I_rlp hStrong h f
    (originalComplex_cellularMembership.{w, wO, ν} c)

end HomotopicalAlgebra.OperadicAcyclicCells.Complexes

namespace HomotopicalAlgebra.OperadicAcyclicCells.Profiles

open CategoryTheory.Operad CategoryTheory.OperadicOrbitCells.ProfileGeometry

variable {W : Type uc} {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C]
  {O : Type wO} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {α : O → Type ui} {D E : (j : O) → α j → W → C}
  (x : ∀ j i, D j i ⟶ E j i) (P : ∀ j, α j → ColoredProfile W)
  (Y : ∀ j i, Action C (Aut (P j i)))
  {X Xprime : C} {f : X ⟶ Xprime}

/-- The original tensor structure is used at every caller-supplied profile occurrence. -/
local instance profileClientFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- Every actual caller cofan, pushout and endpoint of this native complex is retained;
only its original positive profile cell types are classified in the global orbit class. -/
theorem actualProfileComplex_cellularMembership
    (hP : ∀ j i, 0 < inputCount (P j i))
    (hx : ∀ j i k, trivialCofibrations C (x j i ((P j i).inputColor k)))
    (c : RelativeCellComplex.{ν}
      (fun j i => (profileOrbitArrow (x j i) (P j i) (Y j i)).hom) f) :
    cellularClosure.{wO, ν} (orbitGenerators (trivialCofibrations C)).isoClosure f := by
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions
    (coproducts.{ν} (orbitGenerators (trivialCofibrations C)).isoClosure).pushouts O f
  exact (c.transfiniteCompositionOfShape' (fun s =>
    profileOrbitArrow_mem_isoClosure (trivialCofibrations C)
      (x s.j s.i) (P s.j s.i) (hP s.j s.i) (Y s.j s.i) (hx s.j s.i))).mem

variable [UnivLE.{wO, w}] [UnivLE.{ν, w}]

/-- The first route proves couniversal weakness of the same full original native
profile complex, with no left properness or generating-source assumption. -/
theorem actualProfileComplex_weak_transfinite
    [(weakEquivalences C).IsStableUnderTransfiniteComposition.{w}]
    (h : AcyclicSymmetricHMonoidality C)
    (hP : ∀ j i, 0 < inputCount (P j i))
    (hx : ∀ j i k, trivialCofibrations C (x j i ((P j i).inputColor k)))
    (c : RelativeCellComplex.{ν}
      (fun j i => (profileOrbitArrow (x j i) (P j i) (Y j i)).hom) f) :
    couniversalWeakEquivalences C f := by
  have hg : (orbitGenerators (trivialCofibrations C)).isoClosure ≤
      couniversalWeakEquivalences C := (isoClosure_le_iff _ _).2 h.generators_le
  exact cellularClosure_le_couniversal_of_weak_transfinite.{w, wO, ν} _ hg f
    (actualProfileComplex_cellularMembership x P Y hP hx c)

variable [HasLimitsOfSize.{w, w} C] [IsLeftProper C]
  {κ : Cardinal.{wG}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The second route proves the same full profile-complex arrow using the actual
generating I domains and codomains, compact relative to the original cofibration cells. -/
theorem actualProfileComplex_strong_admissible
    (d : CofibrantGenerationData C κ)
    (hStrong : StrongAdmissibleGeneration.{w, ν} C d.I)
    (h : AcyclicSymmetricHMonoidalityOrdinary C)
    (hP : ∀ j i, 0 < inputCount (P j i))
    (hx : ∀ j i k, trivialCofibrations C (x j i ((P j i).inputColor k)))
    (c : RelativeCellComplex.{ν}
      (fun j i => (profileOrbitArrow (x j i) (P j i) (Y j i)).hom) f) :
    couniversalWeakEquivalences C f := by
  let S := cofibrationCells.{w, ν} C
  let _ : S.IsStableUnderCobaseChange := cofibrationCells_stable.1
  let _ : S.IsStableUnderTransfiniteComposition.{w} := cofibrationCells_stable.2.2
  have hg : (orbitGenerators (trivialCofibrations C)).isoClosure ≤
      couniversalWeakEquivalences C := (isoClosure_le_iff _ _).2 h.toCouniversal.generators_le
  have hs : (orbitGenerators (trivialCofibrations C)).isoClosure ≤ S :=
    (isoClosure_le_iff _ _).2 trivialOrbitGenerators_le_cofibrationCells
  exact cellularClosure_le_couniversal_of_compact_independent.{w, wO, ν} d.I S _
    d.I_rlp hStrong cofibrations_le_cofibrationCells hg hs f
    (actualProfileComplex_cellularMembership x P Y hP hx c)

end HomotopicalAlgebra.OperadicAcyclicCells.Profiles

namespace HomotopicalAlgebra.OperadicAcyclicCells.Attachments

open CategoryTheory.Operad CategoryTheory.Operad.Tensor
open CategoryTheory.OperadicOrbitCells.ProfileGeometry
open CategoryTheory.Operad.Tensor.InitialAttachment
open CategoryTheory.Operad.Tensor.InitialAttachment.ProfileCells
open CategoryTheory.Operad.Tensor.Enveloping.Filtration
open CategoryTheory.Operad.Tensor.Enveloping
open CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalSupported

variable {W : Type uc} {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [Small.{us} W] [HasColimitsOfSize.{us, us} C]

/-- The original symmetric tensor structure supplies the original algebra tensors. -/
local instance originalAlgebraFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- Closedness supplies the original tensor-slot colimits. -/
local instance originalAlgebraTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C

/-- The original small color palette supplies its actual profile colimits. -/
local instance originalAlgebraProfiles (d : W) : HasColimitsOfShape (AnalyticIndex W d) C :=
  @hasProfileColimitsOfSmallColors W C inferInstance
    (inferInstance : HasColimitsOfSize.{us, us} C)
    (inferInstance : Small.{us} W) d

/-- The original finite colimits are obtained in the same original source context. -/
local instance originalAlgebraFiniteColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- Evaluation preserves the actual caller colimit via the existing discrete-family
equivalence and the existing functor-category evaluation colimit theorem. -/
local instance originalEvaluationColimits (d : W) {J : Type uj} [Category.{vj} J]
    [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (Pi.eval (fun _ : W => C) d) :=
  preservesColimitsOfShape_of_natIso (piEquivalenceFunctorDiscreteCompEvaluationIso C d)

/-- Evaluation retains the actual original strict-prefix colimits. -/
local instance originalEvaluationContinuous (d : W) :
    PreservesWellOrderContinuousOfShape ℕ (Pi.eval (fun _ : W => C) d) where
  preservesColimitsOfShape _ _ := inferInstance

/-- Both original family cofans, their descendants, every label and both pushout
legs are evaluated at the same original color, without a model on the family category. -/
def evaluatedOriginalStageCells (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A) (d : W) (N : ℕ) :
    AttachCells.{us} (fun p => profileCellMap O A x N p d)
      (((originalHistory O A x y).F ⋙ Pi.eval (fun _ : W => C) d).map
        (homOfLE (Nat.le_succ N))) := by
  let a := familyStageCells O A x y N
  let e := Pi.eval (fun _ : W => C) d
  refine
    { ι := a.ι
      π := a.π
      cofan₁ := Cofan.mk (a.cofan₁.pt d) (fun i => a.cofan₁.inj i d)
      cofan₂ := Cofan.mk (a.cofan₂.pt d) (fun i => a.cofan₂.inj i d)
      isColimit₁ := ?_
      isColimit₂ := ?_
      m := a.m d
      hm := fun i => congrFun (a.hm i) d
      g₁ := a.g₁ d
      g₂ := a.g₂ d
      isPushout := a.isPushout.map e }
  · apply isColimitCofanMkObjOfIsColimit e _ (fun i => a.cofan₁.inj i)
    exact a.isColimit₁.ofIsoColimit (Cofan.ext (Iso.refl _) (by intro i; simp))
  · apply isColimitCofanMkObjOfIsColimit e _ (fun i => a.cofan₂.inj i)
    exact a.isColimit₂.ofIsoColimit (Cofan.ext (Iso.refl _) (by intro i; simp))

/-- The SAME original O,A,x,y old-leg carrier map has the actual native evaluated
relative complex, with the original zeroIso source and original endpoint cocone. -/
def evaluatedOriginalRelativeCellComplex (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A) (d : W) :
    RelativeCellComplex.{us} (fun N p => profileCellMap O A x N p d)
      ((OriginalAttachment.oldMap O A x y).hom d) where
  toTransfiniteCompositionOfShape :=
    (originalRelativeCellComplex O A x y).toTransfiniteCompositionOfShape.map
      (Pi.eval (fun _ : W => C) d)
  attachCells N _ := evaluatedOriginalStageCells O A x y d N

/-- Every occurring original layer has positive degree N+1. At its original output
it is the original Env coefficient orbit; at other colors it is an initial identity. -/
theorem occurringOriginalCell_mem (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime)
    (hx : ∀ r, trivialCofibrations C (x r)) (d : W) (N : ℕ) (p : RawCellIndex W N) :
    (orbitGenerators (trivialCofibrations C)).isoClosure (profileCellMap O A x N p d) := by
  by_cases hd : d = p.1
  · subst d
    have hP : 0 < inputCount (representativeProfile p.1 p.2) := by
      rw [representativeProfile_degree]
      exact Nat.zero_lt_succ N
    have hm := operadProfileArrow_mem_isoClosure (trivialCofibrations C)
      (envelopingOperad O A) x (representativeProfile p.1 p.2) hP (fun i => hx _)
    exact ((orbitGenerators (trivialCofibrations C)).isoClosure.arrow_iso_iff
      (profileCellColorIso O A x N p)).2 hm
  · have hi : IsIso (profileCellMap O A x N p d) := by
      change IsIso (colorMap p.1
        (balancedProfileArrow (envelopingOperad O A) x (representativeProfile p.1 p.2)).hom d)
      dsimp only [colorMap]
      rw [dite_eq_right hd]
      infer_instance
    let _ := hi
    have ht : trivialCofibrations C (profileCellMap O A x N p d) :=
      ⟨(cofibration_iff _).1 inferInstance, (weakEquivalence_iff _).1 inferInstance⟩
    exact le_orbitGenerators_isoClosure (trivialCofibrations C) _ ht

/-- The complete original algebra old leg belongs to the actual global positive orbit
cell class. No nil PP or outcome decomposition premise enters this classification. -/
theorem actualOriginalOldLeg_cellular (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A)
    (hx : ∀ r, trivialCofibrations C (x r)) (d : W) :
    cellularClosure.{0, us} (orbitGenerators (trivialCofibrations C)).isoClosure
      ((OriginalAttachment.oldMap O A x y).hom d) := by
  let c := evaluatedOriginalRelativeCellComplex O A x y d
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions
    (coproducts.{us} (orbitGenerators (trivialCofibrations C)).isoClosure).pushouts ℕ _
  exact (c.transfiniteCompositionOfShape' (fun s =>
    occurringOriginalCell_mem O A x hx d s.j s.i)).mem

/-- The first source route closes the SAME literal original colored algebra pushout
old leg, with every actual O,A,x,y map and original color retained, without properness. -/
theorem actualOriginalOldLeg_weak_transfinite
    [(weakEquivalences C).IsStableUnderTransfiniteComposition.{us}]
    (h : AcyclicSymmetricHMonoidality C) (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A)
    (hx : ∀ r, trivialCofibrations C (x r)) :
    IsPushout y ((freeAlgebraFunctor O).map x) (OriginalAttachment.oldMap O A x y)
        (OriginalAttachment.newMap O A x y) ∧
      ∀ d, couniversalWeakEquivalences C ((OriginalAttachment.oldMap O A x y).hom d) := by
  refine ⟨OriginalAttachment.isPushout O A x y, ?_⟩
  intro d
  have hg : (orbitGenerators (trivialCofibrations C)).isoClosure ≤
      couniversalWeakEquivalences C := (isoClosure_le_iff _ _).2 h.generators_le
  exact cellularClosure_le_couniversal_of_weak_transfinite.{us, 0, us} _ hg _
    (actualOriginalOldLeg_cellular O A x y hx d)

variable [HasLimitsOfSize.{us, us} C] [IsLeftProper C]
  {κ : Cardinal.{wG}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The second source route closes that same original pushout old leg using only
the original I generators, compact on both endpoints relative to the actual source cells. -/
theorem actualOriginalOldLeg_strong_admissible
    (g : CofibrantGenerationData C κ)
    (hStrong : StrongAdmissibleGeneration.{us, us} C g.I)
    (h : AcyclicSymmetricHMonoidalityOrdinary C)
    (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A)
    (hx : ∀ r, trivialCofibrations C (x r)) :
    IsPushout y ((freeAlgebraFunctor O).map x) (OriginalAttachment.oldMap O A x y)
        (OriginalAttachment.newMap O A x y) ∧
      ∀ d, couniversalWeakEquivalences C ((OriginalAttachment.oldMap O A x y).hom d) := by
  refine ⟨OriginalAttachment.isPushout O A x y, ?_⟩
  intro d
  let S := cofibrationCells.{us, us} C
  let _ : S.IsStableUnderCobaseChange := cofibrationCells_stable.1
  let _ : S.IsStableUnderTransfiniteComposition.{us} := cofibrationCells_stable.2.2
  have hg : (orbitGenerators (trivialCofibrations C)).isoClosure ≤
      couniversalWeakEquivalences C := (isoClosure_le_iff _ _).2 h.toCouniversal.generators_le
  have hs : (orbitGenerators (trivialCofibrations C)).isoClosure ≤ S :=
    (isoClosure_le_iff _ _).2 trivialOrbitGenerators_le_cofibrationCells
  exact cellularClosure_le_couniversal_of_compact_independent.{us, 0, us} g.I S _
    g.I_rlp hStrong cofibrations_le_cofibrationCells hg hs _
    (actualOriginalOldLeg_cellular O A x y hx d)

end HomotopicalAlgebra.OperadicAcyclicCells.Attachments

namespace HomotopicalAlgebra.OperadicAcyclicCells.Complexes

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C]

/-- Every arbitrary original product-Sigma coefficient and positive
heterogeneous family retains its actual source, target and cobase-change map. -/
theorem arbitraryCoefficient_actualCobase
    (h : AcyclicSymmetricHMonoidality C) (s : PositiveOrbitFamily C)
    (hs : ∀ r, trivialCofibrations C (s.arrows r).hom)
    {A B : C} (a : (familyOrbitArrow s).left ⟶ A) (q : A ⟶ B)
    (b : (familyOrbitArrow s).right ⟶ B)
    (sq : IsPushout a (familyOrbitArrow s).hom q b) : weakEquivalences C q :=
  h.couniversal s hs A B a q b sq

/-- An actual unary/unit coefficient cofan normalizes the original Arrow,
without a cofibrancy hypothesis on either the coefficient unit or its endpoints. -/
def actualUnaryUnitArrow {A B : C} (f : A ⟶ B) :
    familyOrbitArrow (unaryOrbitFamily f) ≅ Arrow.mk f := unaryOrbitArrowIso f

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] in
/-- The nil attachment history is the original identity, whose actual
pushouts are weak; the empty PP unit arrow is not an input to this proof. -/
theorem nilIdentity_couniversal (A : C) : couniversalWeakEquivalences C (𝟙 A) := by
  intro X Y a q b sq
  let _ : IsIso q := sq.isIso_inl_of_isIso
  exact mem_weakEquivalences q

end HomotopicalAlgebra.OperadicAcyclicCells.Complexes

namespace HomotopicalAlgebra.OperadicAcyclicCells.Complexes

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [HasCoproducts.{w} C]

/-- The exact existing monoid axiom follows from conventional h-monoidality
and the stated acyclic h-cofibration transfinite closure. -/
theorem originalTensorWord_monoidAxiom (h : HMonoidality C)
    [(acyclicHCofibrations C).IsStableUnderTransfiniteComposition.{w}] : MonoidAxiom.{w} C :=
  monoidAxiom_of_hMonoidality h

/-- Every whole original tensor-word cellular arrow is weak under that
actual monoid axiom, with arbitrary tensor coefficients and cofibration endpoints. -/
theorem originalTensorWord_cells_weak (h : HMonoidality C)
    [(acyclicHCofibrations C).IsStableUnderTransfiniteComposition.{w}]
    {X Y : C} (f : X ⟶ Y)
    (hf : transfiniteCompositions.{w}
      (coproducts.{w} (tensorTrivialCofibrationsRight C)).pushouts f) :
    weakEquivalences C f :=
  (originalTensorWord_monoidAxiom h).cellularClosure_le_weakEquivalences f hf

end HomotopicalAlgebra.OperadicAcyclicCells.Complexes


open CategoryTheory Limits Operad Operad.Tensor

namespace HomotopicalAlgebra.OperadicAcyclicCells.Nil

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [Small.{us} W] [HasColimitsOfSize.{us, us} C]

/-- The finite tensor used by the original algebra and filtration. -/
local instance originalFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- Closedness supplies the original tensor-slot colimits. -/
local instance originalTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C

/-- The original small color palette supplies its actual profile colimits. -/
local instance originalProfiles (d : W) : HasColimitsOfShape (AnalyticIndex W d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original source colimits include the actual finite shapes. -/
local instance originalFiniteColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- The actual original O,A,x,y nil-stage map is the original carrier identity
through the genuine original zero-stage isomorphism. -/
def nilStageArrowIso (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A) :
    Arrow.mk (Enveloping.Filtration.zeroIso O A x y).hom ≅ Arrow.mk (𝟙 A.carrier) :=
  Arrow.isoMk (Iso.refl _) (Enveloping.Filtration.zeroIso O A x y).symm (by simp)

/-- Every original color retains its original zero-stage carrier comparison. -/
def nilStageColorIso (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A) (d : W) :
    A.carrier d ≅ ((Enveloping.Filtration.diagram O A x y).obj 0) d where
  hom := (Enveloping.Filtration.zeroIso O A x y).hom d
  inv := (Enveloping.Filtration.zeroIso O A x y).inv d
  hom_inv_id := congrFun (Enveloping.Filtration.zeroIso O A x y).hom_inv_id d
  inv_hom_id := congrFun (Enveloping.Filtration.zeroIso O A x y).inv_hom_id d

variable [HomotopicalAlgebra.ModelCategory C]

/-- The actual original nil carrier comparison is weak at each original color;
no empty pushout-product/unit attachment is used. -/
theorem nilStageColor_weak (O : ColoredOperadObj W C) (A : Algebra O)
    {X Xprime : W → C} (x : X ⟶ Xprime) (y : freeAlgebra O X ⟶ A) (d : W) :
    HomotopicalAlgebra.weakEquivalences C ((Enveloping.Filtration.zeroIso O A x y).hom d) := by
  let e := nilStageColorIso O A x y d
  exact (HomotopicalAlgebra.weakEquivalence_iff _).1
    (inferInstance : HomotopicalAlgebra.WeakEquivalence e.hom)

end HomotopicalAlgebra.OperadicAcyclicCells.Nil
