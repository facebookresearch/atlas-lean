/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Absorption
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.BoundedCellTreeCompactRetract
public import MathlibExtTest.CategoryTheory.SmallObject.CompactRetract.CompactPushoutRetractOwner
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Concrete clients of coherent absorption, idempotent capture and the bounded tree retract

All clients live in `Type` at rank `ℵ₀`.

They check:
* `existsCoherentRetractAbsorption`. The input is a two-successor `Fin 3` composition
  `Bool × Bool → Bool → Unit` of retracts of epimorphisms. Its stage representatives
  `f × Bool` are not identities. The output is a `Fin 3` composition of pushouts of
  epimorphisms that retracts onto the input with identity source maps.
* `CompactRootIdempotentCapture.nonemptyData` on a root-fixed idempotent of
  `ℕ ⊔ Bool` (attached along `Empty`) that collapses both new points to one. It is proved
  idempotent and not the identity. The capture data exists for a `κ`-filtered presentation
  with `ℵ₀`-presentable pieces, supplied by `CompactRootPresentation.existsPresentation`.
* `BoundedCellTreeCompactRetract.existsCompactPushout` on the one-cell tree over `ℕ × Bool`
  of the compact-pushout owner tests. The given retract is a pushout of an `ℵ₀`-presentable
  arrow between `ℵ₀`-presentable objects.
* For the owner tests' epimorphic generator,
  `ArrowRetractRootNormalization.nativeIdempotent` is the identity.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.CoherentRetracts

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

@[expose] public section

namespace MathlibExtTest.CategoryTheory.SmallObject.ConcreteRetractClient

/-- The rank `ℵ₀`. -/
abbrev chi : Cardinal.{0} := Cardinal.aleph0

local instance : Fact chi.IsRegular := Cardinal.fact_isRegular_aleph0

local instance : IsCardinalPresentable Empty chi :=
  (hasCardinalLT_of_finite Empty chi le_rfl).isCardinalPresentable

local instance : IsCardinalPresentable Bool chi :=
  (hasCardinalLT_of_finite Bool chi le_rfl).isCardinalPresentable

local instance : IsCardinalPresentable Unit chi :=
  (hasCardinalLT_of_finite Unit chi le_rfl).isCardinalPresentable

example : IsCardinalLocallyPresentable (Type) chi := inferInstance
example : HasColimitsOfSize.{0, 0} (Type) := inferInstance

/-- The first projection `Bool × Bool → Bool`. -/
def first : Bool × Bool ⟶ Bool := ↾Prod.fst

/-- The map `Bool → Unit`. -/
def second : Bool ⟶ Unit := ↾fun _ => ()

/-- The product `f × Bool`. -/
def lifted {X Y : Type} (f : X ⟶ Y) : X × Bool ⟶ Y × Bool :=
  ↾fun pair => (f pair.1, pair.2)

/-- Every map is a retract of its product with `Bool`. -/
def productRetract {X Y : Type} (f : X ⟶ Y) : RetractArrow f (lifted f) where
  i := Arrow.homMk (↾fun x => (x, false)) (↾fun y => (y, false)) rfl
  r := Arrow.homMk (↾Prod.fst) (↾Prod.fst) rfl
  retract := by ext <;> rfl

/-- The product of a surjection with `Bool` is an epimorphism. -/
theorem lifted_epi {X Y : Type} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Epi (lifted f) := by
  apply (epi_iff_surjective _).2
  rintro ⟨value, bit⟩
  obtain ⟨preimage, hpreimage⟩ := hf value
  exact ⟨(preimage, bit), by change (f preimage, bit) = _; rw [hpreimage]⟩

/-- The epimorphisms of `Type`. -/
abbrev epimorphisms : MorphismProperty (Type) := MorphismProperty.epimorphisms (Type)

/-- The two-successor composition of retracts of epimorphisms. -/
def concreteTransfiniteInput :
    epimorphisms.retracts.TransfiniteCompositionOfShape (Fin 3) (first ≫ second) :=
  MorphismProperty.TransfiniteCompositionOfShape.ofComp first second
    ⟨_, _, lifted first, productRetract first,
      lifted_epi first (fun bit => ⟨(bit, false), rfl⟩)⟩
    ⟨_, _, lifted second, productRetract second,
      lifted_epi second (fun value => ⟨false, by cases value; rfl⟩)⟩

/-- Coherent absorption with identity source maps for the finite input. -/
theorem finiteAbsorptionClient :
    ∃ (Z : Type) (g : Bool × Bool ⟶ Z)
      (_ : epimorphisms.pushouts.TransfiniteCompositionOfShape (Fin 3) g)
      (R : RetractArrow (first ≫ second) g),
      R.i.left = 𝟙 (Bool × Bool) ∧ R.r.left = 𝟙 (Bool × Bool) :=
  existsCoherentRetractAbsorption epimorphisms concreteTransfiniteInput

/-- The empty attaching map into `ℕ`. -/
def emptyRoot : Empty ⟶ ℕ := ↾Empty.elim

/-- The empty cell `Empty → Bool`. -/
def emptyCell : Empty ⟶ Bool := ↾Empty.elim

/-- The pushout `ℕ ⊔ Bool`. -/
abbrev whole : Type := pushout emptyRoot emptyCell

/-- The map collapsing both new points to the image of `false`. -/
def collapsedCell : Bool ⟶ whole :=
  ↾fun _ => pushout.inr emptyRoot emptyCell false

/-- The root-fixed endomorphism collapsing the new points. -/
def nonidentityIdempotent : whole ⟶ whole :=
  pushout.desc (pushout.inl emptyRoot emptyCell) collapsedCell
    (by ext impossible; exact impossible.elim)

/-- The endomorphism fixes the root. -/
theorem idempotent_root :
    pushout.inl emptyRoot emptyCell ≫ nonidentityIdempotent =
      pushout.inl emptyRoot emptyCell := pushout.inl_desc _ _ _

/-- The endomorphism collapses the new points. -/
theorem idempotent_cell :
    pushout.inr emptyRoot emptyCell ≫ nonidentityIdempotent = collapsedCell :=
  pushout.inr_desc _ _ _

/-- The endomorphism is idempotent. -/
theorem idempotent_idempotent :
    nonidentityIdempotent ≫ nonidentityIdempotent = nonidentityIdempotent := by
  apply pushout.hom_ext
  · rw [← Category.assoc, idempotent_root, idempotent_root]
  · rw [← Category.assoc, idempotent_cell]
    ext bit
    exact ConcreteCategory.congr_hom idempotent_cell false

/-- The map `ℕ ⊔ Bool → Bool` sending the root to `false` and the new points identically. -/
def detector : whole ⟶ Bool :=
  pushout.desc (↾fun _ : ℕ => false) (𝟙 Bool)
    (by ext impossible; exact impossible.elim)

/-- The detector restricts to the identity on the new points. -/
theorem detector_cell : pushout.inr emptyRoot emptyCell ≫ detector = 𝟙 Bool :=
  pushout.inr_desc _ _ _

/-- The idempotent is not the identity. -/
theorem idempotent_ne_identity : nonidentityIdempotent ≠ 𝟙 whole := by
  intro hIdentity
  have hCells := idempotent_cell
  rw [hIdentity, Category.comp_id] at hCells
  have hPoint := ConcreteCategory.congr_hom hCells true
  have hDetected := congrArg (fun point => detector point) hPoint
  have hTrue := ConcreteCategory.congr_hom detector_cell true
  have hFalse := ConcreteCategory.congr_hom detector_cell false
  have hContradiction : true = false := hTrue.symm.trans (hDetected.trans hFalse)
  cases hContradiction

/-- Capture data for the non-identity idempotent through a `κ`-filtered root presentation. -/
theorem nonidentityCaptureClient :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsCardinalFiltered J chi)
      (p : ColimitPresentation J (Under.mk emptyRoot)),
      Nonempty (CompactRootIdempotentCapture.Data emptyRoot emptyCell p
        nonidentityIdempotent) ∧
        ∀ j, IsCardinalPresentable (p.diag.obj j).right chi := by
  obtain ⟨J, jCategory, jFiltered, p, hPieces⟩ :=
    CompactRootPresentation.existsPresentation Empty chi emptyRoot
  let : EssentiallySmall.{0} J := essentiallySmall_of_small_of_locallySmall J
  exact ⟨J, jCategory, jFiltered, p,
    CompactRootIdempotentCapture.nonemptyData emptyRoot emptyCell p chi nonidentityIdempotent
      idempotent_root idempotent_idempotent, hPieces⟩

open CompactPushoutRetractOwner

/-- The one-cell tree over `ℕ × Bool` attaching the owner tests' generator. -/
abbrev oneCellTree :
    CellTree (fun _ : Unit => Arrow.mk generator) (ℕ × Bool) (P := PUnit) :=
  CellTree.ofPushout (fun _ : Unit => Arrow.mk generator) (ℕ × Bool) () largeRoot originalArrow
    (pushout.inr largeRoot generator) (IsPushout.of_hasPushout largeRoot generator)

/-- The given retract of the one-cell tree arrow is a pushout of a compact arrow. -/
theorem boundedTreeClient :
    ∃ (D' L : Type) (_ : IsCardinalPresentable D' chi) (_ : IsCardinalPresentable L chi)
      (sourceMap : D' ⟶ ℕ) (replacement : D' ⟶ L)
      (targetMap : L ⟶ pushout givenRoot generator),
      IsPushout sourceMap replacement givenArrow targetMap ∧
        IsCardinalPresentable (Arrow.mk replacement) chi := by
  obtain ⟨D', L, hD, hL, beta, sourceMap, hRoot, replacement, targetMap, hRetract, hPush,
      hArrow⟩ :=
    BoundedCellTreeCompactRetract.existsCompactPushout chi oneCellTree
      (hasCardinalLT_of_finite PUnit chi le_rfl)
      (fun _ => inferInstanceAs (IsCardinalPresentable Bool chi))
      (fun _ => inferInstanceAs (IsCardinalPresentable Unit chi)) originalRetract
  exact ⟨D', L, hD, hL, sourceMap, replacement, targetMap, hPush, hArrow⟩

local instance : Epi generator :=
  (epi_iff_surjective _).2 (fun value => ⟨false, by cases value; rfl⟩)

/-- For the epimorphic generator, the native root-fixed idempotent is the identity. -/
theorem existingOwnerIdempotentIsIdentity :
    ArrowRetractRootNormalization.nativeIdempotent originalRetract largeRoot generator
      (pushout.inr largeRoot generator) (IsPushout.of_hasPushout largeRoot generator) =
        𝟙 _ := by
  apply (cancel_epi (pushout.inl (largeRoot ≫ originalRetract.r.left) generator)).1
  exact (ArrowRetractRootNormalization.nativeRoot_idempotent originalRetract largeRoot
    generator (pushout.inr largeRoot generator)
    (IsPushout.of_hasPushout largeRoot generator)).trans (Category.comp_id _).symm

#print axioms finiteAbsorptionClient
#print axioms nonidentityCaptureClient
#print axioms boundedTreeClient
#print axioms existingOwnerIdempotentIsIdentity

end MathlibExtTest.CategoryTheory.SmallObject.ConcreteRetractClient

end
