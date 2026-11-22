/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyPresheafMonomorphisms
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDiagramSM7
import MathlibExt.AlgebraicTopology.ModelCategory.ScalarInverseHomotopyLimit

/-!
# Reedy monomorphisms, enriched mapping corners, and inverse limits

Relative latching monomorphisms recognize entire simplicial presheaf maps.
The original enriched generator tests control all three mapping-end corners.
Weak inverse-sequence bonds identify its scalar homotopy limit with stage zero,
and the comparison transports every map of such sequences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe uS uD vD w uA uV vV

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite
open CategoryTheory.SimplicialObject
open scoped SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.ReedyRecognitionAPI

section SimplicialMonomorphisms

-- The latching index is small, and both colimit constructions are pointwise.
local instance scalarLatchingColimits (n : ℕ) :
    HasColimitsOfShape (latchingIndex n) SSet.{uS} := by
  letI : Small.{uS} (latchingIndex n) := small_max.{uS} _
  letI : HasColimitsOfShape (latchingIndex n) (Type uS) := Types.hasColimitsOfShape
  exact functorCategoryHasColimitsOfShape
    (J := latchingIndex n) (K := SimplexCategoryᵒᵖ) (C := Type uS)

-- All original relative latching maps determine the monomorphism of the whole diagram.
example {X Y : SimplicialObject SSet.{uS}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, Mono (relativeLatchingMap f n)) : Mono f := by
  have h : reedyLeft (monomorphisms SSet.{uS}) f := hf
  rw [reedyLeft_monomorphisms_eq] at h
  exact h

-- A whole monomorphism supplies the actual relative latching monomorphism at each degree.
example {X Y : SimplicialObject SSet.{uS}} (f : X ⟶ Y) [Mono f] (n : ℕ) :
    Mono (relativeLatchingMap f n) := by
  have h : reedyLeft (monomorphisms SSet.{uS}) f := by
    rw [reedyLeft_monomorphisms_eq]
    exact monomorphisms.infer_property f
  exact h n

variable {D : Type uD} [Category.{vD} D]

local instance presheafLatchingColimits (n : ℕ) :
    HasColimitsOfShape (latchingIndex n) (D ⥤ SSet.{uS}) :=
  functorCategoryHasColimitsOfShape (J := latchingIndex n) (K := D) (C := SSet.{uS})

-- Recognition retains the complete site diagram and gives monic maps at every site and degree.
example {X Y : SimplicialObject (D ⥤ SSet.{uS})} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, Mono (relativeLatchingMap f n))
    (q : SimplexCategoryᵒᵖ) (d : D) : Mono ((f.app q).app d) := by
  have h : reedyLeft (monomorphisms (D ⥤ SSet.{uS})) f := hf
  rw [reedyLeft_presheaf_monomorphisms_eq] at h
  letI : Mono f := h
  infer_instance

-- Sitewise monomorphisms reconstruct the whole map before recognizing its relative latching maps.
example {X Y : SimplicialObject (D ⥤ SSet.{uS})} (f : X ⟶ Y)
    (hf : ∀ (q : SimplexCategoryᵒᵖ) (d : D), Mono ((f.app q).app d)) (n : ℕ) :
    Mono (relativeLatchingMap f n) := by
  letI (q : SimplexCategoryᵒᵖ) (d : D) : Mono ((f.app q).app d) := hf q d
  letI (q : SimplexCategoryᵒᵖ) : Mono (f.app q) := NatTrans.mono_of_mono_app _
  letI : Mono f := NatTrans.mono_of_mono_app _
  have h : reedyLeft (monomorphisms (D ⥤ SSet.{uS})) f := by
    rw [reedyLeft_presheaf_monomorphisms_eq]
    exact monomorphisms.infer_property f
  exact h n

end SimplicialMonomorphisms

section EnrichedMappingCorners

open OriginalEnrichedDiagramSM7

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  [HasProducts.{uA} V] [HasEqualizers V]
  (d : CofibrantGenerationData V κ)
  (s : OriginalEnrichedProjective.SourceConditions (A := A) d)
  (h : GeneratorConditions (A := A) d)

-- The II/JI/IJ tests on the original scalar/free generators extend to the full left classes.
-- Each original I/J right class is converted using the constructed generation datum.
example {F G X Y : EnrichedFunctorCat V A} (i : F ⟶ G) (p : X ⟶ Y)
    (c : MappingCorner i p) :
    ((EnrichedProjective.generators (A := A) d.I).rlp.llp i →
      (EnrichedProjective.generators (A := A) d.J).rlp p → fibrations V c.π) ∧
    ((EnrichedProjective.generators (A := A) d.J).rlp.llp i →
      (EnrichedProjective.generators (A := A) d.J).rlp p → trivialFibrations V c.π) ∧
    ((EnrichedProjective.generators (A := A) d.I).rlp.llp i →
      (EnrichedProjective.generators (A := A) d.I).rlp p → trivialFibrations V c.π) := by
  letI : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
  let E := OriginalEnrichedProjective.generationData d s
  have hiI (hi : (EnrichedProjective.generators (A := A) d.I).rlp.llp i) :
      cofibrations (EnrichedFunctorCat V A) i := by
    have hi' : E.I.rlp.llp i := hi
    rw [E.I_rlp, trivialFibrations_llp] at hi'
    exact hi'
  have hiJ (hi : (EnrichedProjective.generators (A := A) d.J).rlp.llp i) :
      trivialCofibrations (EnrichedFunctorCat V A) i := by
    have hi' : E.J.rlp.llp i := hi
    rw [E.J_rlp, fibrations_llp] at hi'
    exact hi'
  have hpI (hp : (EnrichedProjective.generators (A := A) d.I).rlp p) :
      trivialFibrations (EnrichedFunctorCat V A) p := by
    have hp' : E.I.rlp p := hp
    rw [E.I_rlp] at hp'
    exact hp'
  have hpJ (hp : (EnrichedProjective.generators (A := A) d.J).rlp p) :
      fibrations (EnrichedFunctorCat V A) p := by
    have hp' : E.J.rlp p := hp
    rw [E.J_rlp] at hp'
    exact hp'
  have hs := sm7 d s h
  exact ⟨fun hi hp => hs.1 i p (hiI hi) (hpJ hp) c,
    fun hi hp => hs.2.1 i p (hiJ hi) (hpJ hp) c,
    fun hi hp => hs.2.2 i p (hiI hi) (hpI hp) c⟩

end EnrichedMappingCorners

section InverseSequences

open ScalarInverseHomotopyLimit

-- The actual evaluation/constant adjunction supplies fibrancy in the constructed scalar model.
example (X : SSet.{uS}) [IsFibrant X] :
    letI := DerivedDiagramConstructions.scalarModel.{0, 0, uS} ℕᵒᵖ
    IsFibrant ((Functor.const ℕᵒᵖ).obj X) := by
  letI := DerivedDiagramConstructions.scalarModel.{0, 0, uS} ℕᵒᵖ
  letI : (evaluationConstAdjunction (C := SSet.{uS})).IsQuillenAdjunction :=
    evaluationConst_isQuillen
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := evaluationConstAdjunction (C := SSet.{uS})) inferInstance

-- Weak original successor maps give a weak map of the actual homotopy limits.
example (F : ℕᵒᵖ ⥤ SSet.{uS})
    (hF : ∀ n : ℕ, weakEquivalences SSet.{uS}
      (F.map ((homOfLE (Nat.le_succ n)).op))) :
    WeakEquivalence (limitToZero F) :=
  (weakEquivalence_iff _).mpr (limitToZero_weak F hF)

-- The comparison expresses every whole inverse-sequence map by its original zero component.
example (F G : ℕᵒᵖ ⥤ SSet.{uS})
    [IsFibrant (F.obj zero)] [IsFibrant (G.obj zero)]
    (hF : ∀ n : ℕ, weakEquivalences SSet.{uS}
      (F.map ((homOfLE (Nat.le_succ n)).op)))
    (hG : ∀ n : ℕ, weakEquivalences SSet.{uS}
      (G.map ((homOfLE (Nat.le_succ n)).op))) (a : F ⟶ G) :
    DerivedDiagramConstructions.scalarProjection.{uS}.map
        ((DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, uS} ℕᵒᵖ).map a) =
      (comparisonToZero F hF).hom ≫
        DerivedDiagramConstructions.scalarProjection.{uS}.map (a.app zero) ≫
          (comparisonToZero G hG).inv := by
  apply (cancel_mono (comparisonToZero G hG).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    comparisonToZero_naturality F hF hG a

end InverseSequences

end MathlibExtTest.AlgebraicTopology.ModelCategory.ReedyRecognitionAPI
