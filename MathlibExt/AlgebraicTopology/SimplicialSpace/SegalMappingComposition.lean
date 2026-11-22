/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOver

/-!
# Full composition on the original mapping spaces

Raw representatives use the original degree-two comparison and middle face.
All choices, parameters and coherence are handled by literal simplicial
homotopies on the original mapping fibres.

Source: Rezk (2001), Section 11.2 and Proposition 11.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.SimplicialObject
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner

namespace SimplicialSpace

open SegalHomotopy

private def sectionData {E B : SSet.{u}} (q : E ⟶ B)
    (hq : trivialFibrations SSet.{u} q) :
    (CommSq.mk (show initial.to E ≫ q = initial.to B ≫ (𝟙 B)
      from Subsingleton.elim _ _)).LiftStruct := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff q).mp hq
  letI : Fibration q := hf
  letI : WeakEquivalence q := hw
  letI : Cofibration (initial.to B) := SSet.modelCategoryQuillen.cofibration_of_mono _
  let sq : CommSq (initial.to E) (initial.to B) q (𝟙 B) :=
    ⟨Subsingleton.elim _ _⟩
  exact { l := sq.lift, fac_left := sq.fac_left, fac_right := sq.fac_right }

/-- The full actual section of the original prescribed-vertex triangle comparison. -/
def mappingCompositionSection (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⨯ mappingFibre W y z ⟶ triangleSpace W x y z :=
  (sectionData (triangleComparison W x y z)
    (triangleComparison_trivialFibration W hW x y z)).l

/-- The selected section retains the whole original comparison equation. -/
@[reassoc (attr := simp)]
theorem mappingCompositionSection_comparison (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingCompositionSection W hW x y z ≫ triangleComparison W x y z = 𝟙 _ :=
  (sectionData (triangleComparison W x y z)
    (triangleComparison_trivialFibration W hW x y z)).fac_right

/-- Full simplicial composition uses that same section and original d₁ middle. -/
def mappingComposition (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⨯ mappingFibre W y z ⟶ mappingFibre W x z :=
  mappingCompositionSection W hW x y z ≫ triangleMiddle W x y z

/-- The entire original edge map is the d₁ face of the selected triangle. -/
@[reassoc (attr := simp)]
theorem mappingComposition_fst (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingComposition W hW x y z ≫ mappingFibre.fst W x z =
      mappingCompositionSection W hW x y z ≫ triangleProjection W x y z ≫
        W.diagram.δ (1 : Fin 3) := by
  rw [mappingComposition, Category.assoc, triangleMiddle_fst]

/-- The actual chosen point projection is the original first fibre projection. -/
@[reassoc (attr := simp)]
theorem mappingComposition_snd (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingComposition W hW x y z ≫ mappingFibre.snd W x z =
      prod.fst ≫ mappingFibre.snd W x y := by
  simp only [mappingComposition, Category.assoc, triangleMiddle_snd,
    mappingCompositionSection_comparison_assoc]

/-- Every original product vertex computes the accepted intrinsic composition. -/
theorem mappingComposition_π₀ (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (s : (mappingFibre W x y ⨯ mappingFibre W y z) _⦋0⦌) :
    SSet.π₀.mk ((mappingComposition W hW x y z).app (op ⦋0⦌) s) =
      compose W hW
        (SSet.π₀.mk ((prod.fst : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _).app (op ⦋0⦌) s))
        (SSet.π₀.mk ((prod.snd : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _).app (op ⦋0⦌) s)) := by
  have h := compose_of_triangle W hW x y z
    (SSet.π₀.mk ((mappingCompositionSection W hW x y z).app (op ⦋0⦌) s))
  simp only [SSet.mapπ₀_mk] at h
  change compose W hW
    (SSet.π₀.mk ((mappingCompositionSection W hW x y z ≫
      triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) s))
    (SSet.π₀.mk ((mappingCompositionSection W hW x y z ≫
      triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) s)) =
      SSet.π₀.mk ((mappingComposition W hW x y z).app (op ⦋0⦌) s) at h
  rw [mappingCompositionSection_comparison_assoc,
    mappingCompositionSection_comparison_assoc] at h
  exact h.symm

/-- Postcomposition by an original point is the full original product insertion. -/
def mappingPostcomposition (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (g : (mappingFibre W y z) _⦋0⦌) :
    mappingFibre W x y ⟶ mappingFibre W x z :=
  prod.lift (𝟙 _) (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm g) ≫
    mappingComposition W hW x y z

/-- Precomposition by an original point is the other full original product insertion. -/
def mappingPrecomposition (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    mappingFibre W y z ⟶ mappingFibre W x z :=
  prod.lift (mappingFibre.snd W y z ≫ SSet.yonedaEquiv.symm f) (𝟙 _) ≫
    mappingComposition W hW x y z

private theorem mappingFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : Fibration (mappingFibre.snd W x y) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact ReedyModel.mappingFibre_snd_fibration W x y hW.1

private def endpointShape : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (Fin 2))

private def endpointVertex (i : ULift.{u} (Fin 2)) : (Δ[1] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i.down

private def endpointMap : endpointShape ⟶ (Δ[1] : SSet.{u}) where
  app n := ↾fun i => (SSet.const (X := endpointShape) (endpointVertex i)).app n i
  naturality {n m} φ := by
    ext i
    have h := congrArg (fun f : endpointShape.obj n ⟶ (Δ[1] : SSet.{u}).obj m => f i)
      ((SSet.const (X := endpointShape) (endpointVertex i)).naturality φ)
    change (SSet.const (X := endpointShape) (endpointVertex i)).app m i =
      (Δ[1] : SSet.{u}).map φ ((SSet.const (X := endpointShape) (endpointVertex i)).app n i) at h
    exact h

private theorem endpointMap_zero (i : ULift.{u} (Fin 2)) :
    endpointMap.app (op ⦋0⦌) i = endpointVertex i := by
  change (Δ[1] : SSet.{u}).map (⦋0⦌.const ⦋0⦌ 0).op (endpointVertex i) = _
  have h : ⦋0⦌.const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by decide
  rw [h, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]

private theorem endpointMap_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((endpointMap.{u}).app n) := by
  intro i j hij
  let φ : n ⟶ op ⦋0⦌ := (⦋0⦌.const n.unop 0).op
  have hn (k : ULift.{u} (Fin 2)) :
      endpointMap.app (op ⦋0⦌) k = (Δ[1] : SSet.{u}).map φ (endpointMap.app n k) := by
    have h := congrArg (fun f : endpointShape.obj n ⟶ (Δ[1] : SSet.{u}).obj (op ⦋0⦌) =>
      f k) (endpointMap.naturality φ)
    change endpointMap.app (op ⦋0⦌) k =
      (Δ[1] : SSet.{u}).map φ (endpointMap.app n k) at h
    exact h
  have hzero := (hn i).trans ((congrArg ((Δ[1] : SSet.{u}).map φ) hij).trans (hn j).symm)
  have hvertices : endpointVertex i = endpointVertex j :=
    (endpointMap_zero.{u} i).symm.trans (hzero.trans (endpointMap_zero.{u} j))
  apply ULift.ext
  have hdown := congrArg SSet.stdSimplex.obj₀Equiv hvertices
  simpa only [endpointVertex, Equiv.apply_symm_apply] using hdown

private theorem endpointMap_mono : Mono (endpointMap : endpointShape ⟶ (Δ[1] : SSet.{u})) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  exact endpointMap_injective n

private theorem tensorEndpoint_mono (A : SSet.{u}) : Mono (A ◁ endpointMap) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  change (x.1, endpointMap.app n x.2) = (y.1, endpointMap.app n y.2) at h
  apply Prod.ext
  · exact congrArg (fun z : A.obj n × (Δ[1] : SSet.{u}).obj n => z.1) h
  · exact endpointMap_injective n
      (congrArg (fun z : A.obj n × (Δ[1] : SSet.{u}).obj n => z.2) h)

private def endpointIn (A : SSet.{u}) (i : Fin 2) : A ⟶ A ⊗ endpointShape :=
  CartesianMonoidalCategory.lift (𝟙 A)
    (SSet.const (X := A) (Y := endpointShape) (ULift.up i))

private def endpointTop {A E : SSet.{u}} (s₀ s₁ : A ⟶ E) : A ⊗ endpointShape ⟶ E where
  app n := ↾fun ⟨a, i⟩ => if i.down = 0 then s₀.app n a else s₁.app n a
  naturality {n m} φ := by
    ext ⟨a, i⟩
    change (if i.down = 0 then s₀.app m (A.map φ a) else s₁.app m (A.map φ a)) =
      E.map φ (if i.down = 0 then s₀.app n a else s₁.app n a)
    split_ifs
    · exact congrArg (fun f : A.obj n ⟶ E.obj m => f a) (s₀.naturality φ)
    · exact congrArg (fun f : A.obj n ⟶ E.obj m => f a) (s₁.naturality φ)

private theorem endpointIn_zero_map (A : SSet.{u}) :
    endpointIn A 0 ≫ (A ◁ endpointMap) = (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) := by
  apply SSet.hom_ext
  intro n
  ext a
  dsimp [endpointIn, endpointMap, endpointShape, endpointVertex, SSet.ι₀, SSet.const]
  rfl

private theorem endpointIn_one_map (A : SSet.{u}) :
    endpointIn A 1 ≫ (A ◁ endpointMap) = (SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) := by
  apply SSet.hom_ext
  intro n
  ext a
  dsimp [endpointIn, endpointMap, endpointShape, endpointVertex, SSet.ι₁, SSet.const]
  rfl

private theorem endpointIn_zero_top {A E : SSet.{u}} (s₀ s₁ : A ⟶ E) :
    endpointIn A 0 ≫ endpointTop s₀ s₁ = s₀ := by
  ext n a
  rfl

private theorem endpointIn_one_top {A E : SSet.{u}} (s₀ s₁ : A ⟶ E) :
    endpointIn A 1 ≫ endpointTop s₀ s₁ = s₁ := by
  ext n a
  rfl

private def prescribedLift {A E B : SSet.{u}} (q : E ⟶ B)
    (hq : trivialFibrations SSet.{u} q) (b : A ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (s₀ s₁ : A ⟶ E) (h₀ : s₀ ≫ q = SSet.ι₀ ≫ b) (h₁ : s₁ ≫ q = SSet.ι₁ ≫ b) :
    {H : A ⊗ (Δ[1] : SSet.{u}) ⟶ E //
      SSet.ι₀ ≫ H = s₀ ∧ SSet.ι₁ ≫ H = s₁ ∧ H ≫ q = b} := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff q).mp hq
  letI : Fibration q := hf
  letI : WeakEquivalence q := hw
  letI : Mono (endpointMap : endpointShape ⟶ (Δ[1] : SSet.{u})) := endpointMap_mono
  letI : Mono (A ◁ endpointMap) := tensorEndpoint_mono A
  letI : Cofibration (A ◁ endpointMap) := SSet.modelCategoryQuillen.cofibration_of_mono _
  have hsq : endpointTop s₀ s₁ ≫ q = (A ◁ endpointMap) ≫ b := by
    ext n ⟨a, ⟨i⟩⟩
    fin_cases i
    · change q.app n (s₀.app n a) = b.app n (SSet.ι₀.app n a)
      exact congrArg (fun f : A ⟶ B => f.app n a) h₀
    · change q.app n (s₁.app n a) = b.app n (SSet.ι₁.app n a)
      exact congrArg (fun f : A ⟶ B => f.app n a) h₁
  let sq : CommSq (endpointTop s₀ s₁) (A ◁ endpointMap) q b := ⟨hsq⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← endpointIn_zero_map, Category.assoc, sq.fac_left, endpointIn_zero_top]
  · rw [← endpointIn_one_map, Category.assoc, sq.fac_left, endpointIn_one_top]

/-- Lift every actual base homotopy with both original endpoints and whole projection. -/
def mappingCompositionLiftHomotopy (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) {A : SSet.{u}}
    (b : A ⊗ (Δ[1] : SSet.{u}) ⟶ mappingFibre W x y ⨯ mappingFibre W y z)
    (s₀ s₁ : A ⟶ triangleSpace W x y z)
    (h₀ : s₀ ≫ triangleComparison W x y z = SSet.ι₀ ≫ b)
    (h₁ : s₁ ≫ triangleComparison W x y z = SSet.ι₁ ≫ b) :
    {H : A ⊗ (Δ[1] : SSet.{u}) ⟶ triangleSpace W x y z //
      SSet.ι₀ ≫ H = s₀ ∧ SSet.ι₁ ≫ H = s₁ ∧ H ≫ triangleComparison W x y z = b} :=
  prescribedLift (triangleComparison W x y z)
    (triangleComparison_trivialFibration W hW x y z) b s₀ s₁ h₀ h₁

private def literalHomotopy {A B : SSet.{u}} {f g : A ⟶ B}
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B) (h₀ : SSet.ι₀ ≫ h = f) (h₁ : SSet.ι₁ ≫ h = g) :
    SSet.Homotopy f g :=
  (show SSet.HomotopyRel f g (⊥ : A.Subcomplex) from
    { h := h
      h₀ := h₀
      h₁ := h₁
      stationary := by intro n a ha t; cases ha }).toHomotopy

/-- Any prescribed base interval and its endpoint lifts give the full composite homotopy. -/
def mappingCompositionHomotopy (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) {A : SSet.{u}}
    (b : A ⊗ (Δ[1] : SSet.{u}) ⟶ mappingFibre W x y ⨯ mappingFibre W y z)
    (s₀ s₁ : A ⟶ triangleSpace W x y z)
    (h₀ : s₀ ≫ triangleComparison W x y z = SSet.ι₀ ≫ b)
    (h₁ : s₁ ≫ triangleComparison W x y z = SSet.ι₁ ≫ b) :
    SSet.Homotopy (s₀ ≫ triangleMiddle W x y z) (s₁ ≫ triangleMiddle W x y z) := by
  let H := mappingCompositionLiftHomotopy W hW x y z b s₀ s₁ h₀ h₁
  refine literalHomotopy (H.val ≫ triangleMiddle W x y z) ?_ ?_
  · rw [← Category.assoc, H.property.1]
  · rw [← Category.assoc, H.property.2.1]

private def triangleChoice {W : SimplicialSpace.{u}} (hW : segalSpaces W)
    {x y z : (W.diagram _⦋0⦌) _⦋0⦌} {A : SSet.{u}}
    (b : A ⟶ mappingFibre W x y ⨯ mappingFibre W y z)
    (s₀ s₁ : A ⟶ triangleSpace W x y z)
    (h₀ : s₀ ≫ triangleComparison W x y z = b)
    (h₁ : s₁ ≫ triangleComparison W x y z = b) :
    SSet.Homotopy (s₀ ≫ triangleMiddle W x y z) (s₁ ≫ triangleMiddle W x y z) :=
  mappingCompositionHomotopy W hW x y z
    (CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ b) s₀ s₁
    (by simpa only [SSet.ι₀_fst_assoc] using h₀)
    (by simpa only [SSet.ι₁_fst_assoc] using h₁)

private def homotopyPost {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (k : B ⟶ C) : SSet.Homotopy (f ≫ k) (g ≫ k) :=
  literalHomotopy (H.h ≫ k)
    (by rw [← Category.assoc, H.h₀])
    (by rw [← Category.assoc, H.h₁])

private def homotopyPre {A B C : SSet.{u}} {f g : B ⟶ C}
    (H : SSet.Homotopy f g) (k : A ⟶ B) : SSet.Homotopy (k ≫ f) (k ≫ g) :=
  literalHomotopy ((k ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    (by rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀])
    (by rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁])

private def homotopyPairLeft {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (c : A ⟶ C) :
    SSet.Homotopy (prod.lift f c) (prod.lift g c) := by
  refine literalHomotopy
    (prod.lift H.h (CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ c)) ?_ ?_
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, H.h₀, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, SSet.ι₀_fst_assoc, prod.lift_snd]
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, H.h₁, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, SSet.ι₁_fst_assoc, prod.lift_snd]

private def homotopyPairRight {A B C : SSet.{u}} {f g : A ⟶ C}
    (b : A ⟶ B) (H : SSet.Homotopy f g) :
    SSet.Homotopy (prod.lift b f) (prod.lift b g) := by
  refine literalHomotopy
    (prod.lift (CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ b) H.h) ?_ ?_
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, SSet.ι₀_fst_assoc, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, H.h₀, prod.lift_snd]
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, SSet.ι₁_fst_assoc, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, H.h₁, prod.lift_snd]

private def homotopyOverPoint {A B : SSet.{u}} {f g : A ⟶ B}
    (p : B ⟶ (Δ[0] : SSet.{u})) (H : SSet.Homotopy f g) :
    SSet.HomotopyRelOver p f g (⊥ : A.Subcomplex) where
  toHomotopyRel :=
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      stationary := by intro n a ha t; cases ha }
  over := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private def homotopyReverse {A B : SSet.{u}} {f g : A ⟶ B}
    (p : B ⟶ (Δ[0] : SSet.{u})) [Fibration p] (H : SSet.Homotopy f g) :
    SSet.Homotopy g f :=
  (SSet.HomotopyRelOver.symm (homotopyOverPoint p H)).toHomotopyRel.toHomotopy

private def homotopyJoin {A B : SSet.{u}} {f g h : A ⟶ B}
    (p : B ⟶ (Δ[0] : SSet.{u})) [Fibration p]
    (H₀ : SSet.Homotopy f g) (H₁ : SSet.Homotopy g h) :
    SSet.Homotopy f h :=
  (SSet.HomotopyRelOver.trans (homotopyOverPoint p H₀)
    (homotopyOverPoint p H₁)).toHomotopyRel.toHomotopy

private theorem identityPoint_fst (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.yonedaEquiv.symm (identityVertex W x) ≫ mappingFibre.fst W x x =
      SSet.yonedaEquiv.symm x ≫ W.diagram.σ (0 : Fin 1) := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, identityVertex_fst]

private def unitPairLeft (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ mappingFibre W x x ⨯ mappingFibre W x y :=
  prod.lift (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm (identityVertex W x)) (𝟙 _)

private def unitPairRight (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ mappingFibre W x y ⨯ mappingFibre W y y :=
  prod.lift (𝟙 _) (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm (identityVertex W y))

private def unitTriangleLeft (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : mappingFibre W x y ⟶ triangleSpace W x x y :=
  pullback.lift (mappingFibre.fst W x y ≫ W.diagram.σ (0 : Fin 2))
    (unitPairLeft W x y) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          unitPairLeft, prod.lift_fst_assoc]
        have hs : W.diagram.σ (0 : Fin 2) ≫ W.diagram.δ (2 : Fin 3) =
            W.diagram.δ (1 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) :=
          W.diagram.δ_comp_σ_of_gt (n := 0) (i := (1 : Fin 2))
            (j := (0 : Fin 1)) (by decide)
        rw [hs]
        rw [mappingFibre.source_eq_assoc, identityPoint_fst]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          unitPairLeft, prod.lift_snd_assoc, Category.id_comp]
        have hs : W.diagram.σ (0 : Fin 2) ≫ W.diagram.δ (0 : Fin 3) = 𝟙 _ :=
          W.diagram.δ_comp_σ_self (i := (0 : Fin 2))
        rw [hs, Category.comp_id])

private def unitTriangleRight (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : mappingFibre W x y ⟶ triangleSpace W x y y :=
  pullback.lift (mappingFibre.fst W x y ≫ W.diagram.σ (1 : Fin 2))
    (unitPairRight W x y) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          unitPairRight, prod.lift_fst_assoc, Category.id_comp]
        have hs : W.diagram.σ (1 : Fin 2) ≫ W.diagram.δ (2 : Fin 3) = 𝟙 _ :=
          W.diagram.δ_comp_σ_succ (i := (1 : Fin 2))
        rw [hs, Category.comp_id]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          unitPairRight, prod.lift_snd_assoc]
        have hs : W.diagram.σ (1 : Fin 2) ≫ W.diagram.δ (0 : Fin 3) =
            W.diagram.δ (0 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) :=
          W.diagram.δ_comp_σ_of_le (n := 0) (i := (0 : Fin 2))
            (j := (0 : Fin 1)) (by decide)
        rw [hs]
        rw [mappingFibre.target_eq_assoc, identityPoint_fst])

private theorem unitTriangleLeft_comparison (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    unitTriangleLeft W x y ≫ triangleComparison W x x y = unitPairLeft W x y :=
  pullback.lift_snd _ _ _

private theorem unitTriangleRight_comparison (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    unitTriangleRight W x y ≫ triangleComparison W x y y = unitPairRight W x y :=
  pullback.lift_snd _ _ _

private theorem unitTriangleLeft_middle (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    unitTriangleLeft W x y ≫ triangleMiddle W x x y = 𝟙 (mappingFibre W x y) := by
  have hf : (unitTriangleLeft W x y ≫ triangleMiddle W x x y) ≫ mappingFibre.fst W x y =
      (𝟙 (mappingFibre W x y)) ≫ mappingFibre.fst W x y := by
    rw [Category.assoc, triangleMiddle_fst]
    have hp : unitTriangleLeft W x y ≫ triangleProjection W x x y =
        mappingFibre.fst W x y ≫ W.diagram.σ (0 : Fin 2) := pullback.lift_fst _ _ _
    have hs : W.diagram.σ (0 : Fin 2) ≫ W.diagram.δ (1 : Fin 3) = 𝟙 _ :=
      W.diagram.δ_comp_σ_succ (i := (0 : Fin 2))
    rw [← Category.assoc, hp, Category.assoc, hs, Category.comp_id, Category.id_comp]
  exact pullback.hom_ext hf (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem unitTriangleRight_middle (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    unitTriangleRight W x y ≫ triangleMiddle W x y y = 𝟙 (mappingFibre W x y) := by
  have hf : (unitTriangleRight W x y ≫ triangleMiddle W x y y) ≫ mappingFibre.fst W x y =
      (𝟙 (mappingFibre W x y)) ≫ mappingFibre.fst W x y := by
    rw [Category.assoc, triangleMiddle_fst]
    have hp : unitTriangleRight W x y ≫ triangleProjection W x y y =
        mappingFibre.fst W x y ≫ W.diagram.σ (1 : Fin 2) := pullback.lift_fst _ _ _
    have hs : W.diagram.σ (1 : Fin 2) ≫ W.diagram.δ (1 : Fin 3) = 𝟙 _ :=
      W.diagram.δ_comp_σ_self (i := (1 : Fin 2))
    rw [← Category.assoc, hp, Category.assoc, hs, Category.comp_id, Category.id_comp]
  exact pullback.hom_ext hf (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The full original left-unit map is literally homotopic to identity. -/
def mappingCompositionLeftUnit (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy
      (prod.lift (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm (identityVertex W x)) (𝟙 _) ≫
        mappingComposition W hW x x y) (𝟙 (mappingFibre W x y)) := by
  have H := triangleChoice hW (unitPairLeft W x y)
    (unitPairLeft W x y ≫ mappingCompositionSection W hW x x y)
    (unitTriangleLeft W x y) (by rw [Category.assoc, mappingCompositionSection_comparison,
      Category.comp_id]) (unitTriangleLeft_comparison W x y)
  simpa only [unitPairLeft, mappingComposition, Category.assoc, unitTriangleLeft_middle] using H

/-- The full original right-unit map has the other literal unit homotopy. -/
def mappingCompositionRightUnit (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy
      (prod.lift (𝟙 _) (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm (identityVertex W y)) ≫
        mappingComposition W hW x y y) (𝟙 (mappingFibre W x y)) := by
  have H := triangleChoice hW (unitPairRight W x y)
    (unitPairRight W x y ≫ mappingCompositionSection W hW x y y)
    (unitTriangleRight W x y) (by rw [Category.assoc, mappingCompositionSection_comparison,
      Category.comp_id]) (unitTriangleRight_comparison W x y)
  simpa only [unitPairRight, mappingComposition, Category.assoc, unitTriangleRight_middle] using H

private abbrev tripleProduct (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :=
  (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z

private abbrev tetrahedronSpace (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :=
  pullback (threeEdgeComparison W) (threeEdgePair W w x y z)

private abbrev tetrahedronProjection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSpace W w x y z ⟶ W.diagram _⦋3⦌ := pullback.fst _ _

private abbrev tetrahedronComparison (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSpace W w x y z ⟶ tripleProduct W w x y z := pullback.snd _ _

private theorem tetrahedron_condition (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫ threeEdgeComparison W =
      tetrahedronComparison W w x y z ≫ threeEdgePair W w x y z := pullback.condition

private theorem tetrahedron_first (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫
        W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin 3)).op =
      tetrahedronComparison W w x y z ≫ prod.fst ≫ prod.fst ≫ mappingFibre.fst W w x := by
  rw [← threeEdgeComparison_first, ← Category.assoc, tetrahedron_condition]
  rw [Category.assoc, threeEdgePair_first]

private theorem tetrahedron_second (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫
        W.diagram.map (SimplexCategory.mkOfSucc (1 : Fin 3)).op =
      tetrahedronComparison W w x y z ≫ prod.fst ≫ prod.snd ≫ mappingFibre.fst W x y := by
  rw [← threeEdgeComparison_second, ← Category.assoc, tetrahedron_condition]
  rw [Category.assoc, threeEdgePair_second]

private theorem tetrahedron_third (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronProjection W w x y z ≫
        W.diagram.map (SimplexCategory.mkOfSucc (2 : Fin 3)).op =
      tetrahedronComparison W w x y z ≫ prod.snd ≫ mappingFibre.fst W y z := by
  rw [← threeEdgeComparison_third, ← Category.assoc, tetrahedron_condition]
  rw [Category.assoc, threeEdgePair_third]

private theorem tetrahedron_trivialFibration (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (tetrahedronComparison W w x y z) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp (threeEdgeComparison_trivialFibration W hW)
  let := hf
  let := hw
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

private def tetrahedronSection (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tripleProduct W w x y z ⟶ tetrahedronSpace W w x y z :=
  (sectionData (tetrahedronComparison W w x y z)
    (tetrahedron_trivialFibration W hW w x y z)).l

@[reassoc (attr := simp)]
private theorem tetrahedronSection_comparison (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSection W hW w x y z ≫ tetrahedronComparison W w x y z = 𝟙 _ :=
  (sectionData (tetrahedronComparison W w x y z)
    (tetrahedron_trivialFibration W hW w x y z)).fac_right

private theorem face_edge_eq (W : SimplicialSpace.{u})
    (i : Fin 4) (j : Fin 3) (e : ⦋1⦌ ⟶ ⦋3⦌)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = e) :
    W.diagram.δ i ≫ W.diagram.δ j = W.diagram.map e.op := by
  change W.diagram.map (SimplexCategory.δ i).op ≫
    W.diagram.map (SimplexCategory.δ j).op = _
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, h]

private def tetrahedron012 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSpace W w x y z ⟶ triangleSpace W w x y :=
  pullback.lift (tetrahedronProjection W w x y z ≫ W.diagram.δ (3 : Fin 4))
    (tetrahedronComparison W w x y z ≫ prod.fst) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst]
        rw [face_edge_eq W 3 2 (SimplexCategory.mkOfSucc (0 : Fin 3)) (by decide)]
        exact tetrahedron_first W w x y z
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd]
        rw [face_edge_eq W 3 0 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide)]
        exact tetrahedron_second W w x y z)

private def tetrahedron123 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSpace W w x y z ⟶ triangleSpace W x y z :=
  pullback.lift (tetrahedronProjection W w x y z ≫ W.diagram.δ (0 : Fin 4))
    (prod.lift (tetrahedronComparison W w x y z ≫ prod.fst ≫ prod.snd)
      (tetrahedronComparison W w x y z ≫ prod.snd)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.lift_fst_assoc]
        rw [face_edge_eq W 0 2 (SimplexCategory.mkOfSucc (1 : Fin 3)) (by decide)]
        exact tetrahedron_second W w x y z
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          prod.lift_snd_assoc]
        rw [face_edge_eq W 0 0 (SimplexCategory.mkOfSucc (2 : Fin 3)) (by decide)]
        exact tetrahedron_third W w x y z)

@[reassoc]
private theorem tetrahedron012_projection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron012 W w x y z ≫ triangleProjection W w x y =
      tetrahedronProjection W w x y z ≫ W.diagram.δ (3 : Fin 4) := pullback.lift_fst _ _ _

@[reassoc]
private theorem tetrahedron123_projection (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron123 W w x y z ≫ triangleProjection W x y z =
      tetrahedronProjection W w x y z ≫ W.diagram.δ (0 : Fin 4) := pullback.lift_fst _ _ _

private theorem tetrahedron012_comparison (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron012 W w x y z ≫ triangleComparison W w x y =
      tetrahedronComparison W w x y z ≫ prod.fst := pullback.lift_snd _ _ _

private theorem tetrahedron123_comparison (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron123 W w x y z ≫ triangleComparison W x y z =
      prod.lift (tetrahedronComparison W w x y z ≫ prod.fst ≫ prod.snd)
        (tetrahedronComparison W w x y z ≫ prod.snd) := pullback.lift_snd _ _ _

private def tetrahedron023 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSpace W w x y z ⟶ triangleSpace W w y z :=
  pullback.lift (tetrahedronProjection W w x y z ≫ W.diagram.δ (1 : Fin 4))
    (prod.lift (tetrahedron012 W w x y z ≫ triangleMiddle W w x y)
      (tetrahedronComparison W w x y z ≫ prod.snd)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.lift_fst_assoc, triangleMiddle_fst]
        rw [tetrahedron012_projection_assoc]
        rw [face_edge_eq W 1 2 (SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide)) (by decide),
          face_edge_eq W 3 1 (SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide)) (by decide)]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd, prod.lift_snd_assoc]
        rw [face_edge_eq W 1 0 (SimplexCategory.mkOfSucc (2 : Fin 3)) (by decide)]
        exact tetrahedron_third W w x y z)

private def tetrahedron013 (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedronSpace W w x y z ⟶ triangleSpace W w x z :=
  pullback.lift (tetrahedronProjection W w x y z ≫ W.diagram.δ (2 : Fin 4))
    (prod.lift (tetrahedronComparison W w x y z ≫ prod.fst ≫ prod.fst)
      (tetrahedron123 W w x y z ≫ triangleMiddle W x y z)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst, prod.lift_fst_assoc]
        rw [face_edge_eq W 2 2 (SimplexCategory.mkOfSucc (0 : Fin 3)) (by decide)]
        exact tetrahedron_first W w x y z
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          prod.lift_snd_assoc, triangleMiddle_fst]
        rw [tetrahedron123_projection_assoc]
        rw [face_edge_eq W 2 0 (SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide)) (by decide),
          face_edge_eq W 0 1 (SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide)) (by decide)])

private theorem tetrahedron023_comparison (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron023 W w x y z ≫ triangleComparison W w y z =
      prod.lift (tetrahedron012 W w x y z ≫ triangleMiddle W w x y)
        (tetrahedronComparison W w x y z ≫ prod.snd) := pullback.lift_snd _ _ _

private theorem tetrahedron013_comparison (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron013 W w x y z ≫ triangleComparison W w x z =
      prod.lift (tetrahedronComparison W w x y z ≫ prod.fst ≫ prod.fst)
        (tetrahedron123 W w x y z ≫ triangleMiddle W x y z) := pullback.lift_snd _ _ _

private theorem tetrahedron_long_edge (W : SimplicialSpace.{u})
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    tetrahedron023 W w x y z ≫ triangleMiddle W w y z =
      tetrahedron013 W w x y z ≫ triangleMiddle W w x z := by
  have hf : (tetrahedron023 W w x y z ≫ triangleMiddle W w y z) ≫ mappingFibre.fst W w z =
      (tetrahedron013 W w x y z ≫ triangleMiddle W w x z) ≫ mappingFibre.fst W w z := by
    rw [Category.assoc, triangleMiddle_fst, Category.assoc, triangleMiddle_fst]
    have h₁ : tetrahedron023 W w x y z ≫ triangleProjection W w y z =
        tetrahedronProjection W w x y z ≫ W.diagram.δ (1 : Fin 4) := pullback.lift_fst _ _ _
    have h₂ : tetrahedron013 W w x y z ≫ triangleProjection W w x z =
        tetrahedronProjection W w x y z ≫ W.diagram.δ (2 : Fin 4) := pullback.lift_fst _ _ _
    rw [← Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, Category.assoc,
      face_edge_eq W 1 1 (SimplexCategory.mkOfLe (0 : Fin 4) 3 (by decide)) (by decide),
      face_edge_eq W 2 1 (SimplexCategory.mkOfLe (0 : Fin 4) 3 (by decide)) (by decide)]
  exact pullback.hom_ext hf (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- Full binary associativity on the original threefold product, via all four faces. -/
def mappingCompositionAssoc (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy
      (prod.lift
        ((prod.fst : (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ _) ≫
          mappingComposition W hW w x y)
        prod.snd ≫ mappingComposition W hW w y z)
      (prod.lift
        ((prod.fst : (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ _) ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ mappingComposition W hW x y z) ≫
          mappingComposition W hW w x z) := by
  let P := tripleProduct W w x y z
  let τ := tetrahedronSection W hW w x y z
  let a : P ⟶ mappingFibre W w x := prod.fst ≫ prod.fst
  let b : P ⟶ mappingFibre W x y := prod.fst ≫ prod.snd
  let c : P ⟶ mappingFibre W y z := prod.snd
  let ab : P ⟶ mappingFibre W w y := τ ≫ tetrahedron012 W w x y z ≫ triangleMiddle W w x y
  let bc : P ⟶ mappingFibre W x z := τ ≫ tetrahedron123 W w x y z ≫ triangleMiddle W x y z

  have hab : SSet.Homotopy
      ((prod.fst : P ⟶ _) ≫ mappingComposition W hW w x y) ab := by
    have H := triangleChoice hW (prod.fst : P ⟶ mappingFibre W w x ⨯ mappingFibre W x y)
      (prod.fst ≫ mappingCompositionSection W hW w x y)
      (τ ≫ tetrahedron012 W w x y z)
      (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id])
      (by simp only [τ, Category.assoc, tetrahedron012_comparison,
        tetrahedronSection_comparison_assoc])
    simpa only [ab, mappingComposition, Category.assoc] using H

  have hbc : SSet.Homotopy
      (prod.lift b c ≫ mappingComposition W hW x y z) bc := by
    have hq : (τ ≫ tetrahedron123 W w x y z) ≫ triangleComparison W x y z =
        prod.lift b c := by
      apply prod.hom_ext
      · simp only [τ, b, Category.assoc, tetrahedron123_comparison,
          prod.lift_fst, tetrahedronSection_comparison_assoc]
      · simp only [τ, c, Category.assoc, tetrahedron123_comparison,
          prod.lift_snd, tetrahedronSection_comparison_assoc]
    have H := triangleChoice hW (prod.lift b c)
      (prod.lift b c ≫ mappingCompositionSection W hW x y z)
      (τ ≫ tetrahedron123 W w x y z)
      (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id]) hq
    simpa only [bc, mappingComposition, Category.assoc] using H

  have h023 : SSet.Homotopy
      (prod.lift ab c ≫ mappingComposition W hW w y z)
      (τ ≫ tetrahedron023 W w x y z ≫ triangleMiddle W w y z) := by
    have hq : (τ ≫ tetrahedron023 W w x y z) ≫ triangleComparison W w y z =
        prod.lift ab c := by
      apply prod.hom_ext
      · simp only [ab, Category.assoc, tetrahedron023_comparison, prod.lift_fst]
      · simp only [τ, c, Category.assoc, tetrahedron023_comparison, prod.lift_snd,
          tetrahedronSection_comparison_assoc]
    have H := triangleChoice hW (prod.lift ab c)
      (prod.lift ab c ≫ mappingCompositionSection W hW w y z)
      (τ ≫ tetrahedron023 W w x y z)
      (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id]) hq
    simpa only [mappingComposition, Category.assoc] using H

  have h013 : SSet.Homotopy
      (prod.lift a bc ≫ mappingComposition W hW w x z)
      (τ ≫ tetrahedron013 W w x y z ≫ triangleMiddle W w x z) := by
    have hq : (τ ≫ tetrahedron013 W w x y z) ≫ triangleComparison W w x z =
        prod.lift a bc := by
      apply prod.hom_ext
      · simp only [τ, a, Category.assoc, tetrahedron013_comparison, prod.lift_fst,
          tetrahedronSection_comparison_assoc]
      · simp only [bc, Category.assoc, tetrahedron013_comparison, prod.lift_snd]
    have H := triangleChoice hW (prod.lift a bc)
      (prod.lift a bc ≫ mappingCompositionSection W hW w x z)
      (τ ≫ tetrahedron013 W w x y z)
      (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id]) hq
    simpa only [mappingComposition, Category.assoc] using H

  letI : Fibration (mappingFibre.snd W w z) := mappingFibration W hW w z
  have HL := homotopyJoin (mappingFibre.snd W w z)
    (homotopyPost (homotopyPairLeft hab c) (mappingComposition W hW w y z)) h023
  have HR := homotopyJoin (mappingFibre.snd W w z)
    (homotopyPost (homotopyPairRight a hbc) (mappingComposition W hW w x z)) h013
  have he : τ ≫ tetrahedron023 W w x y z ≫ triangleMiddle W w y z =
      τ ≫ tetrahedron013 W w x y z ≫ triangleMiddle W w x z := by
    exact congrArg (fun f : tetrahedronSpace W w x y z ⟶ mappingFibre W w z => τ ≫ f)
      (tetrahedron_long_edge W w x y z)
  have HR' : SSet.Homotopy
      (prod.lift a (prod.lift b c ≫ mappingComposition W hW x y z) ≫
        mappingComposition W hW w x z)
      (τ ≫ tetrahedron023 W w x y z ≫ triangleMiddle W w y z) := by
    rw [he]
    exact HR
  exact homotopyJoin (mappingFibre.snd W w z) HL
    (homotopyReverse (mappingFibre.snd W w z) HR')

private def triangleMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ triangleSpace V (mappingVertexMap f x) (mappingVertexMap f y)
      (mappingVertexMap f z) :=
  pullback.lift (triangleProjection W x y z ≫ f.hom.app (op ⦋2⦌))
    (triangleComparison W x y z ≫
      prod.map (mappingFibre.map f (x := x) (y := y) rfl rfl)
        (mappingFibre.map f (x := y) (y := z) rfl rfl)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.map_fst_assoc, mappingFibre.map_fst]
        rw [← SimplicialObject.δ_naturality f.hom (2 : Fin 3),
          triangleProjection_first_assoc]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          prod.map_snd_assoc, mappingFibre.map_fst]
        rw [← SimplicialObject.δ_naturality f.hom (0 : Fin 3),
          triangleProjection_last_assoc])

@[reassoc]
private theorem triangleMap_projection {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleMap f x y z ≫ triangleProjection V (mappingVertexMap f x) (mappingVertexMap f y)
        (mappingVertexMap f z) = triangleProjection W x y z ≫ f.hom.app (op ⦋2⦌) :=
  pullback.lift_fst _ _ _

private theorem triangleMap_comparison {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleMap f x y z ≫ triangleComparison V (mappingVertexMap f x) (mappingVertexMap f y)
        (mappingVertexMap f z) =
      triangleComparison W x y z ≫
        prod.map (mappingFibre.map f (x := x) (y := y) rfl rfl)
          (mappingFibre.map f (x := y) (y := z) rfl rfl) :=
  pullback.lift_snd _ _ _

private theorem triangleMap_middle {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleMap f x y z ≫ triangleMiddle V (mappingVertexMap f x) (mappingVertexMap f y)
        (mappingVertexMap f z) =
      triangleMiddle W x y z ≫ mappingFibre.map f (x := x) (y := z) rfl rfl := by
  have hf :
      (triangleMap f x y z ≫ triangleMiddle V (mappingVertexMap f x) (mappingVertexMap f y)
        (mappingVertexMap f z)) ≫
          mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f z) =
      (triangleMiddle W x y z ≫ mappingFibre.map f (x := x) (y := z) rfl rfl) ≫
        mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f z) := by
    simp only [Category.assoc, triangleMiddle_fst, mappingFibre.map_fst,
      triangleMiddle_fst_assoc, triangleMap_projection_assoc]
    rw [← SimplicialObject.δ_naturality f.hom (1 : Fin 3)]
  exact pullback.hom_ext hf (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- Full composition is homotopy natural on the original transported mapping fibres. -/
def mappingCompositionNaturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy
      (mappingComposition W hW x y z ≫ mappingFibre.map f (x := x) (y := z) rfl rfl)
      (prod.map (mappingFibre.map f (x := x) (y := y) rfl rfl)
        (mappingFibre.map f (x := y) (y := z) rfl rfl) ≫
          mappingComposition V hV (mappingVertexMap f x) (mappingVertexMap f y)
            (mappingVertexMap f z)) := by
  let c := prod.map (mappingFibre.map f (x := x) (y := y) rfl rfl)
    (mappingFibre.map f (x := y) (y := z) rfl rfl)
  have h₀ : (mappingCompositionSection W hW x y z ≫ triangleMap f x y z) ≫
      triangleComparison V (mappingVertexMap f x) (mappingVertexMap f y) (mappingVertexMap f z) =
        c := by
    rw [Category.assoc, triangleMap_comparison, mappingCompositionSection_comparison_assoc]
  have H := triangleChoice hV c
    (mappingCompositionSection W hW x y z ≫ triangleMap f x y z)
    (c ≫ mappingCompositionSection V hV (mappingVertexMap f x) (mappingVertexMap f y)
      (mappingVertexMap f z)) h₀
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id])
  simpa only [c, mappingComposition, Category.assoc, triangleMap_middle] using H

/-- Every full triangle map is homotopic to the selected composite of its two edges. -/
def mappingCompositionOfTriangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy (triangleMiddle W x y z)
      (triangleComparison W x y z ≫ mappingComposition W hW x y z) := by
  have H := triangleChoice hW (triangleComparison W x y z)
    (𝟙 (triangleSpace W x y z))
    (triangleComparison W x y z ≫ mappingCompositionSection W hW x y z)
    (by rw [Category.id_comp])
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id])
  simpa only [mappingComposition, Category.assoc, Category.id_comp] using H

@[reassoc]
private theorem point_comp {A B : SSet.{u}} (f : A ⟶ B) (a : A _⦋0⦌) :
    SSet.yonedaEquiv.symm a ≫ f = SSet.yonedaEquiv.symm (f.app (op ⦋0⦌) a) := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

private def associativityParameter (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) {A : SSet.{u}}
    (a : A ⟶ mappingFibre W w x) (b : A ⟶ mappingFibre W x y)
    (c : A ⟶ mappingFibre W y z) :
    SSet.Homotopy
      (prod.lift (prod.lift a b ≫ mappingComposition W hW w x y) c ≫
        mappingComposition W hW w y z)
      (prod.lift a (prod.lift b c ≫ mappingComposition W hW x y z) ≫
        mappingComposition W hW w x z) := by
  have H := homotopyPre (mappingCompositionAssoc W hW w x y z) (prod.lift (prod.lift a b) c)
  simpa only [Category.assoc, prod.comp_lift_assoc, prod.lift_fst_assoc, prod.lift_snd_assoc,
    prod.lift_fst, prod.lift_snd] using H

private theorem pair_eta {A B C : SSet.{u}} (f : A ⟶ B ⨯ C) :
    prod.lift (f ≫ prod.fst) (f ≫ prod.snd) = f := by
  apply prod.hom_ext
  · rw [prod.lift_fst]
  · rw [prod.lift_snd]

/-- Every prescribed original triangle gives the full postcomposition associativity law. -/
def mappingPostcompositionTriangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) (k : (triangleSpace W x y z) _⦋0⦌) :
    SSet.Homotopy
      (mappingPostcomposition W hW w x z ((triangleMiddle W x y z).app (op ⦋0⦌) k))
      (mappingPostcomposition W hW w x y
        ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k) ≫
          mappingPostcomposition W hW w y z
            ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k)) := by
  let A := mappingFibre W w x
  let d : A ⟶ triangleSpace W x y z :=
    mappingFibre.snd W w x ≫ SSet.yonedaEquiv.symm k
  let b : A ⟶ mappingFibre W x y := d ≫ triangleComparison W x y z ≫ prod.fst
  let c : A ⟶ mappingFibre W y z := d ≫ triangleComparison W x y z ≫ prod.snd
  have Htri := homotopyPre (mappingCompositionOfTriangle W hW x y z) d
  have Hmid := homotopyPost (homotopyPairRight (𝟙 A) Htri) (mappingComposition W hW w x z)
  have Hmid' : SSet.Homotopy
      (mappingPostcomposition W hW w x z ((triangleMiddle W x y z).app (op ⦋0⦌) k))
      (prod.lift (𝟙 A) (prod.lift b c ≫ mappingComposition W hW x y z) ≫
        mappingComposition W hW w x z) := by
    have he : prod.lift b c = d ≫ triangleComparison W x y z := by
      simpa only [b, c, Category.assoc] using pair_eta (d ≫ triangleComparison W x y z)
    rw [he]
    simpa only [mappingPostcomposition, d, Category.assoc, point_comp,
      SSet.comp_app, CategoryTheory.comp_apply] using Hmid
  have Hassoc := associativityParameter W hW w x y z (𝟙 A) b c
  have Hassoc' : SSet.Homotopy
      (mappingPostcomposition W hW w x y
        ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k) ≫
          mappingPostcomposition W hW w y z
            ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k))
      (prod.lift (𝟙 A) (prod.lift b c ≫ mappingComposition W hW x y z) ≫
        mappingComposition W hW w x z) := by
    have hb : b = mappingFibre.snd W w x ≫
        SSet.yonedaEquiv.symm ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k) := by
      simpa only [b, d, Category.assoc] using
        congrArg (fun f => mappingFibre.snd W w x ≫ f)
          (point_comp (triangleComparison W x y z ≫ prod.fst) k)
    have hc : c = mappingFibre.snd W w x ≫
        SSet.yonedaEquiv.symm ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k) := by
      simpa only [c, d, Category.assoc] using
        congrArg (fun f => mappingFibre.snd W w x ≫ f)
          (point_comp (triangleComparison W x y z ≫ prod.snd) k)
    have hs : (prod.lift (𝟙 A) b ≫ mappingComposition W hW w x y) ≫
        mappingFibre.snd W w y = mappingFibre.snd W w x := by
      rw [Category.assoc, mappingComposition_snd, prod.lift_fst_assoc, Category.id_comp]
    have he : mappingPostcomposition W hW w x y
        ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k) ≫
        mappingPostcomposition W hW w y z
          ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k) =
        prod.lift (prod.lift (𝟙 A) b ≫ mappingComposition W hW w x y) c ≫
          mappingComposition W hW w y z := by
      unfold mappingPostcomposition
      rw [← hb]
      rw [← Category.assoc]
      apply congrArg (fun f => f ≫ mappingComposition W hW w y z)
      apply prod.hom_ext
      · rw [Category.assoc, prod.lift_fst, Category.comp_id, prod.lift_fst]
      · rw [Category.assoc, prod.lift_snd, ← Category.assoc, hs, ← hc, prod.lift_snd]
    rw [he]
    exact Hassoc
  letI : Fibration (mappingFibre.snd W w z) := mappingFibration W hW w z
  exact homotopyJoin (mappingFibre.snd W w z) Hmid'
    (homotopyReverse (mappingFibre.snd W w z) Hassoc')

/-- The other prescribed-triangle law retains the original precomposition order. -/
def mappingPrecompositionTriangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z t : (W.diagram _⦋0⦌) _⦋0⦌) (k : (triangleSpace W x y z) _⦋0⦌) :
    SSet.Homotopy
      (mappingPrecomposition W hW x z t ((triangleMiddle W x y z).app (op ⦋0⦌) k))
      (mappingPrecomposition W hW y z t
        ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k) ≫
          mappingPrecomposition W hW x y t
            ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k)) := by
  let A := mappingFibre W z t
  let d : A ⟶ triangleSpace W x y z :=
    mappingFibre.snd W z t ≫ SSet.yonedaEquiv.symm k
  let a : A ⟶ mappingFibre W x y := d ≫ triangleComparison W x y z ≫ prod.fst
  let b : A ⟶ mappingFibre W y z := d ≫ triangleComparison W x y z ≫ prod.snd
  have Htri := homotopyPre (mappingCompositionOfTriangle W hW x y z) d
  have Hmid := homotopyPost (homotopyPairLeft Htri (𝟙 A)) (mappingComposition W hW x z t)
  have Hmid' : SSet.Homotopy
      (mappingPrecomposition W hW x z t ((triangleMiddle W x y z).app (op ⦋0⦌) k))
      (prod.lift (prod.lift a b ≫ mappingComposition W hW x y z) (𝟙 A) ≫
        mappingComposition W hW x z t) := by
    have he : prod.lift a b = d ≫ triangleComparison W x y z := by
      simpa only [a, b, Category.assoc] using pair_eta (d ≫ triangleComparison W x y z)
    rw [he]
    simpa only [mappingPrecomposition, d, Category.assoc, point_comp,
      SSet.comp_app, CategoryTheory.comp_apply] using Hmid
  have Hassoc := associativityParameter W hW x y z t a b (𝟙 A)
  have Hassoc' : SSet.Homotopy
      (prod.lift (prod.lift a b ≫ mappingComposition W hW x y z) (𝟙 A) ≫
        mappingComposition W hW x z t)
      (mappingPrecomposition W hW y z t
        ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k) ≫
          mappingPrecomposition W hW x y t
            ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k)) := by
    have ha : a = mappingFibre.snd W z t ≫
        SSet.yonedaEquiv.symm ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k) := by
      simpa only [a, d, Category.assoc] using
        congrArg (fun f => mappingFibre.snd W z t ≫ f)
          (point_comp (triangleComparison W x y z ≫ prod.fst) k)
    have hb : b = mappingFibre.snd W z t ≫
        SSet.yonedaEquiv.symm ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k) := by
      simpa only [b, d, Category.assoc] using
        congrArg (fun f => mappingFibre.snd W z t ≫ f)
          (point_comp (triangleComparison W x y z ≫ prod.snd) k)
    have hs : (prod.lift b (𝟙 A) ≫ mappingComposition W hW y z t) ≫
        mappingFibre.snd W y t = mappingFibre.snd W z t :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have he : mappingPrecomposition W hW y z t
        ((triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌) k) ≫
        mappingPrecomposition W hW x y t
          ((triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌) k) =
        prod.lift a (prod.lift b (𝟙 A) ≫ mappingComposition W hW y z t) ≫
          mappingComposition W hW x y t := by
      unfold mappingPrecomposition
      rw [← hb]
      rw [← Category.assoc]
      apply congrArg (fun f => f ≫ mappingComposition W hW x y t)
      apply prod.hom_ext
      · rw [Category.assoc, prod.lift_fst, ← Category.assoc, hs, ← ha, prod.lift_fst]
      · rw [Category.assoc, prod.lift_snd, Category.comp_id, prod.lift_snd]
    rw [he]
    exact Hassoc
  letI : Fibration (mappingFibre.snd W x t) := mappingFibration W hW x t
  exact homotopyJoin (mappingFibre.snd W x t) Hmid' Hassoc'

/-- Any original valid lift is compared with the selected lift over its whole base map. -/
def mappingCompositionChoice (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) {A : SSet.{u}}
    (b : A ⟶ mappingFibre W x y ⨯ mappingFibre W y z)
    (s : A ⟶ triangleSpace W x y z) (hs : s ≫ triangleComparison W x y z = b) :
    SSet.Homotopy (s ≫ triangleMiddle W x y z) (b ≫ mappingComposition W hW x y z) := by
  have H := triangleChoice hW b s (b ≫ mappingCompositionSection W hW x y z) hs
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id])
  simpa only [mappingComposition, Category.assoc] using H

/-- An actual fixed-fibre point homotopy varies the entire postcomposition operator. -/
def mappingPostcompositionVariation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (g g' : (mappingFibre W y z) _⦋0⦌)
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm g) (SSet.yonedaEquiv.symm g')) :
    SSet.Homotopy (mappingPostcomposition W hW x y z g) (mappingPostcomposition W hW x y z g') := by
  exact homotopyPost (homotopyPairRight (𝟙 _)
    (homotopyPre H (mappingFibre.snd W x y))) (mappingComposition W hW x y z)

/-- Fixed-fibre point variation also preserves the other whole point operator. -/
def mappingPrecompositionVariation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (f f' : (mappingFibre W x y) _⦋0⦌)
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm f) (SSet.yonedaEquiv.symm f')) :
    SSet.Homotopy (mappingPrecomposition W hW x y z f) (mappingPrecomposition W hW x y z f') := by
  exact homotopyPost (homotopyPairLeft (homotopyPre H (mappingFibre.snd W y z)) (𝟙 _))
    (mappingComposition W hW x y z)

/-- Postcomposition is homotopy natural with the actual transported original point. -/
def mappingPostcompositionNaturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (g : (mappingFibre W y z) _⦋0⦌) :
    SSet.Homotopy
      (mappingPostcomposition W hW x y z g ≫ mappingFibre.map f (x := x) (y := z) rfl rfl)
      (mappingFibre.map f (x := x) (y := y) rfl rfl ≫
        mappingPostcomposition V hV (mappingVertexMap f x) (mappingVertexMap f y)
          (mappingVertexMap f z) ((mappingFibre.map f (x := y) (y := z) rfl rfl).app
              (op ⦋0⦌) g)) := by
  let i := prod.lift (𝟙 (mappingFibre W x y))
    (mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm g)
  have he : i ≫ prod.map (mappingFibre.map f (x := x) (y := y) rfl rfl)
      (mappingFibre.map f (x := y) (y := z) rfl rfl) =
      mappingFibre.map f (x := x) (y := y) rfl rfl ≫
        prod.lift (𝟙 _) (mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) ≫
          SSet.yonedaEquiv.symm
            ((mappingFibre.map f (x := y) (y := z) rfl rfl).app (op ⦋0⦌) g)) := by
    apply prod.hom_ext
    · simp only [i, Category.assoc, prod.map_fst, prod.lift_fst_assoc, Category.id_comp,
        prod.lift_fst, Category.comp_id]
    · simp only [i, Category.assoc, prod.map_snd, prod.lift_snd_assoc, prod.lift_snd,
        mappingFibre.map_snd_assoc, point_comp]
  have H := homotopyPre (mappingCompositionNaturality f hW hV x y z) i
  have hh : SSet.Homotopy
      (i ≫ mappingComposition W hW x y z ≫ mappingFibre.map f (x := x) (y := z) rfl rfl)
      (mappingFibre.map f (x := x) (y := y) rfl rfl ≫
        prod.lift (𝟙 _) (mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) ≫
          SSet.yonedaEquiv.symm
            ((mappingFibre.map f (x := y) (y := z) rfl rfl).app (op ⦋0⦌) g)) ≫
              mappingComposition V hV (mappingVertexMap f x) (mappingVertexMap f y)
                (mappingVertexMap f z)) := by
    simpa only [Category.assoc, reassoc_of% he] using H
  exact hh

/-- Precomposition retains the analogous transported-point homotopy naturality. -/
def mappingPrecompositionNaturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    SSet.Homotopy
      (mappingPrecomposition W hW x y z a ≫ mappingFibre.map f (x := x) (y := z) rfl rfl)
      (mappingFibre.map f (x := y) (y := z) rfl rfl ≫
        mappingPrecomposition V hV (mappingVertexMap f x) (mappingVertexMap f y)
          (mappingVertexMap f z) ((mappingFibre.map f (x := x) (y := y) rfl rfl).app
              (op ⦋0⦌) a)) := by
  let i := prod.lift (mappingFibre.snd W y z ≫ SSet.yonedaEquiv.symm a) (𝟙 (mappingFibre W y z))
  have he : i ≫ prod.map (mappingFibre.map f (x := x) (y := y) rfl rfl)
      (mappingFibre.map f (x := y) (y := z) rfl rfl) =
      mappingFibre.map f (x := y) (y := z) rfl rfl ≫
        prod.lift (mappingFibre.snd V (mappingVertexMap f y) (mappingVertexMap f z) ≫
          SSet.yonedaEquiv.symm
            ((mappingFibre.map f (x := x) (y := y) rfl rfl).app (op ⦋0⦌) a)) (𝟙 _) := by
    apply prod.hom_ext
    · simp only [i, Category.assoc, prod.map_fst, prod.lift_fst_assoc, prod.lift_fst,
        mappingFibre.map_snd_assoc, point_comp]
    · simp only [i, Category.assoc, prod.map_snd, prod.lift_snd_assoc, Category.id_comp,
        prod.lift_snd, Category.comp_id]
  have H := homotopyPre (mappingCompositionNaturality f hW hV x y z) i
  have hh : SSet.Homotopy
      (i ≫ mappingComposition W hW x y z ≫ mappingFibre.map f (x := x) (y := z) rfl rfl)
      (mappingFibre.map f (x := y) (y := z) rfl rfl ≫
        prod.lift (mappingFibre.snd V (mappingVertexMap f y) (mappingVertexMap f z) ≫
          SSet.yonedaEquiv.symm
            ((mappingFibre.map f (x := x) (y := y) rfl rfl).app (op ⦋0⦌) a)) (𝟙 _) ≫
              mappingComposition V hV (mappingVertexMap f x) (mappingVertexMap f y)
                (mappingVertexMap f z)) := by
    simpa only [Category.assoc, reassoc_of% he] using H
  exact hh

end SimplicialSpace
