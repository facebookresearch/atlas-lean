/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Original coproduct closure from cobase and transfinite composition.
module

public import MathlibExt.CategoryTheory.MorphismProperty.CoproductCellDecomposition
public import Mathlib.SetTheory.Cardinal.Order

/-! # Coproduct closure from original pushout cells

The original Sigma.map is the SAME native colimit composite of the supplied
original arrows. Only cobase/transfinite stability and structural coproduct
existence are inputs. No LLP, factorization, Smith or model data is supplied.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- The original whole coproduct map belongs to any cobase/transfinite-stable property. -/
theorem coproductMap_mem_of_cobase_transfinite
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{w}]
    {ι : Type w} [HasColimitsOfShape (Discrete ι) C]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  classical
  -- This is the public universe transfer, not a Type0 family replacement.
  let _ : P.IsStableUnderTransfiniteComposition.{0} :=
    IsStableUnderTransfiniteComposition.shrink₀ (W := P)
  have hIso : isomorphisms C ≤ P := by
    intro X Y g hg
    let _ : IsIso g := hg
    let e : Arrow.mk (𝟙 X) ≅ Arrow.mk g :=
      Arrow.isoMk (Iso.refl X) (asIso g) (by simp)
    let t := (TransfiniteCompositionOfShape.id P X).ofArrowIso e
    exact P.transfiniteCompositionsOfShape_le (Fin 1) _ t.mem
  have hFamily : ofHoms f ≤ P := (ofHoms_le_iff f P).2 hf
  have hPush : (ofHoms f).pushouts ≤ P :=
    (pushouts_le_iff (P := ofHoms f) (Q := P)).2 hFamily
  have hCells : isomorphisms C ⊔ (ofHoms f).pushouts ≤ P :=
    sup_le hIso hPush
  -- The order is confined to this proof, retaining EVERY original label.
  obtain ⟨linear, wellFounded⟩ := exists_wellFoundedLT ι
  let _ : LinearOrder ι := linear
  let _ : WellFoundedLT ι := wellFounded
  let _ : SuccOrder (CoproductCells.cellOrder ι) :=
    SuccOrder.ofLinearWellFoundedLT (CoproductCells.cellOrder ι)
  obtain ⟨raw⟩ := CoproductCells.coproductMap_originalCells f
  let t := raw.ofLE hCells
  -- ofLE preserves raw.F, isoBot, incl, full IsColimit and strict fac exactly.
  exact P.transfiniteCompositionsOfShape_le (CoproductCells.cellOrder ι) _ t.mem

/-- The same property is stable under all original coproducts in the stated index universe. -/
theorem isStableUnderCoproducts_of_cobase_transfinite
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{w}] [HasCoproducts.{w} C] :
    P.IsStableUnderCoproducts.{w} := by
  have hTransfinite : P.IsStableUnderTransfiniteComposition.{w} := inferInstance
  let _ : P.IsStableUnderTransfiniteComposition.{0} :=
    IsStableUnderTransfiniteComposition.shrink₀ (W := P)
  -- This actual Fin2 proof derives iso-invariance; it is not a caller outcome.
  let _ : P.RespectsIso := RespectsIso.of_respects_arrow_iso P (by
    intro a b e ha
    let t := (TransfiniteCompositionOfShape.ofMem (W := P) a.hom ha).ofArrowIso e
    exact P.transfiniteCompositionsOfShape_le (Fin 2) _ t.mem)
  refine { isStableUnderCoproductsOfShape := fun (ι : Type w) => ?_ }
  refine IsStableUnderCoproductsOfShape.mk (W := P) ι ?_
  intro A B _ _ f hf
  exact @coproductMap_mem_of_cobase_transfinite C inferInstance P inferInstance
    hTransfinite ι inferInstance A B f hf

end CategoryTheory.MorphismProperty
