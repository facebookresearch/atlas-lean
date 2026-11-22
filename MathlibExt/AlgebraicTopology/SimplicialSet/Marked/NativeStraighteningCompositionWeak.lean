/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningRelativeComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningInnerParameterWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseMarkRefinementWeak

/-!
# Actual native weakness of original composition-mark parameter cells

The same original native map of an actual coherent-model fibration
reflects relative composition along every original full triangle.
Tensoring that original triangle with each whole marked parameter edge
gives genuine composition marking lifts for arbitrary diagrams. The
same native adjunction proves the actual scalar composition images are
trivial cofibrations. The original full parameter pushout and both side
equations then give all maximal scalar-mono corners by actual pushout
closure and two-out-of-three in the original target model. No target
weakness, native filler, diagram fibrancy or Quillen result is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] vertexDecidableEq markedSimplicialCategory enrichedDiagramCategory
  coefficientMarkedModelCategory

/-- Every same whole original native composition triangle retains its relative marked long edge under an actual
coherent-model fibration. -/
theorem nativeUnstraightening_map_relativeCompStruct (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G)
    {x₀ x₁ x₂ : (nativeUnstraighteningTotal B F).toSSet _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (H : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : e₀₁.edge ∈ (nativeUnstraighteningTotal B F).marking)
    (h₁₂ : e₁₂.edge ∈ (nativeUnstraighteningTotal B F).marking)
    (h₀₂ : ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌) e₀₂.edge ∈
      (nativeUnstraighteningTotal B G).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → e₀₂.edge ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let t := yonedaEquiv.symm H.simplex
  have face (k : Fin 3) : (nativeUnstraighteningTotal B F).toSSet.δ k H.simplex =
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ k)) := by
    have hf := (stdSimplex.yonedaEquiv_δ_comp t k).symm.trans (yonedaEquiv_comp _ t)
    have ht : yonedaEquiv t = H.simplex := Equiv.apply_symm_apply _ _
    rw [ht] at hf
    exact hf
  have h₂ := (face 2).symm.trans H.d₂
  have h₀ := (face 0).symm.trans H.d₀
  have h₁ := (face 1).symm.trans H.d₁
  have ht₂ : t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈
      (nativeUnstraighteningTotal B F).marking := by rw [h₂]; exact h₀₁
  have ht₀ : t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈
      (nativeUnstraighteningTotal B F).marking := by rw [h₀]; exact h₁₂
  have ht₁ : (t ≫ ((nativeUnstraightening B).map q).left.hom).app (op ⦋1⦌) compositionLongEdge.{u} ∈
      (nativeUnstraighteningTotal B G).marking := by
    change ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌)
      (t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3)))) ∈ _
    rw [h₁]
    exact h₀₂
  exact h₁ ▸ nativeUnstraightening_map_relativeComposition B q hq t ht₂ ht₀ ht₁

/-- The same original composition marking cell lifts every actual native map of a coherent-model fibration over any
original base. -/
theorem nativeUnstraightening_map_compositionLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty compositionCell.{u} ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p := ((nativeUnstraightening B).map q).left
  refine ⟨fun {t b} sq => ?_⟩
  have hw : t.hom ≫ p.hom = b.hom :=
    (congrArg Hom.hom sq.w).trans (Category.id_comp _)
  have h₂ := t.preserve (show yonedaEquiv (stdSimplex.δ (2 : Fin 3)) ∈ compositionCellSource.{u}.marking from
    Or.inr (Or.inl rfl))
  have h₀ := t.preserve (show yonedaEquiv (stdSimplex.δ (0 : Fin 3)) ∈ compositionCellSource.{u}.marking from
    Or.inr (Or.inr rfl))
  have hb := b.preserve (show compositionLongEdge.{u} ∈ compositionCellTarget.{u}.marking from Or.inr (Or.inl rfl))
  have h₁ : (t.hom ≫ p.hom).app (op ⦋1⦌) compositionLongEdge.{u} ∈
      (nativeUnstraighteningTotal B G).marking := hw.symm ▸ hb
  have hd := nativeUnstraightening_map_relativeComposition B q hq t.hom h₂ h₀ h₁
  let l : compositionCellTarget.{u} ⟶ nativeUnstraighteningTotal B F := ofWithEdges t.hom (by
    intro e he
    rcases he with he | he
    · exact he ▸ hd
    · exact t.preserve (Or.inr he))
  exact CommSq.HasLift.mk' ⟨l, Hom.ext (Category.id_comp _), Hom.ext hw⟩

/-- The entire original marked parameter prism preserves relative composition and lifts the same actual native
model-fibration map. -/
theorem nativeUnstraightening_map_compositionTensorLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (P : Marked.{u}) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (prodMap (𝟙 P) compositionCell.{u}) ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p := ((nativeUnstraightening B).map q).left
  refine ⟨fun {t b} sq => ?_⟩
  have hw : t.hom ≫ p.hom = b.hom := by
    have h := congrArg Hom.hom sq.w
    change t.hom ≫ p.hom = (𝟙 (P.toSSet ⊗ (Δ[2] : SSet.{u}))) ≫ b.hom at h
    exact h.trans (Category.id_comp _)
  have hd (a : P.toSSet _⦋1⦌) (ha : a ∈ P.marking) :
      t.hom.app (op ⦋1⦌) (a, compositionLongEdge.{u}) ∈ (nativeUnstraighteningTotal B F).marking := by
    obtain ⟨x₀, x₁, x₂, c, d, e, H, hH⟩ :=
      Edge.CompStruct.exists_of_simplex (yonedaEquiv (𝟙 (Δ[2] : SSet.{u})))
    have face (i : Fin 3) : (Δ[2] : SSet.{u}).δ i H.simplex = yonedaEquiv (stdSimplex.δ i) := by
      rw [hH, ← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id]
    have hc : c.edge = yonedaEquiv (stdSimplex.δ (2 : Fin 3)) := H.d₂.symm.trans (face 2)
    have he : e.edge = compositionLongEdge.{u} := H.d₁.symm.trans (face 1)
    have hd' : d.edge = yonedaEquiv (stdSimplex.δ (0 : Fin 3)) := H.d₀.symm.trans (face 0)
    let a' := Edge.mk' a
    let v := (a'.tensor c).map t.hom
    let w := ((Edge.id (P.toSSet.δ 0 a)).tensor d).map t.hom
    let z := (a'.tensor e).map t.hom
    have hv : v.edge ∈ (nativeUnstraighteningTotal B F).marking :=
      @t.preserve (a, c.edge) ⟨ha, Or.inr (Or.inl hc)⟩
    have hw' : w.edge ∈ (nativeUnstraighteningTotal B F).marking :=
      @t.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), d.edge)
        ⟨P.degenerate_mem _, Or.inr (Or.inr hd')⟩
    have hz : p.hom.app (op ⦋1⦌) z.edge ∈ (nativeUnstraighteningTotal B G).marking := by
      have hm := b.preserve (show (a, compositionLongEdge.{u}) ∈
        (prod P compositionCellTarget.{u}).marking from ⟨ha, Or.inr (Or.inl rfl)⟩)
      have hmap : (show P.toSSet ⊗ (Δ[2] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet from t.hom) ≫
          p.hom = b.hom := hw
      have h := congrArg
        (fun f : P.toSSet ⊗ (Δ[2] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet =>
          f.app (op ⦋1⦌) (a, compositionLongEdge.{u})) hmap
      change p.hom.app (op ⦋1⦌) (t.hom.app (op ⦋1⦌) (a, e.edge)) ∈ _
      rw [he]
      exact h.symm ▸ hm
    let T : Edge.CompStruct v w z := ((Edge.CompStruct.compId a').tensor H).map t.hom
    have h := nativeUnstraightening_map_relativeCompStruct B q T hv hw' hz hq
    change t.hom.app (op ⦋1⦌) (a, e.edge) ∈ _ at h
    exact he ▸ h
  let l : prod P compositionCellTarget.{u} ⟶ nativeUnstraighteningTotal B F :=
    { hom := t.hom
      preserve {e} he := by
        rcases he.2 with hdeg | hlong | hshort
        · exact @t.preserve e ⟨he.1, Or.inl hdeg⟩
        · change t.hom.app (op ⦋1⦌) (e.1, e.2) ∈ (nativeUnstraighteningTotal B F).marking
          rw [show e.2 = compositionLongEdge.{u} from hlong]
          exact hd e.1 he.1
        · exact @t.preserve e ⟨he.1, Or.inr hshort⟩ }
  exact CommSq.HasLift.mk' ⟨l, Hom.ext (Category.id_comp _), Hom.ext hw⟩

/-- The same original maximal scalar composition cell retains its full marked slice lift and complete original base
projection. -/
theorem nativeUnstraightening_map_compositionScalarLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (K : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty
      (((overParameterBifunctor (max B)).map (compositionCellOver r)).app K) ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let _ : HasLiftingProperty
      ((((overParameterBifunctor (max B)).map (compositionCellOver r)).app K).left)
        ((nativeUnstraightening B).map q).left :=
    nativeUnstraightening_map_compositionTensorLifting B q (max K) hq
  exact HasLiftingProperty.over _ ((nativeUnstraightening B).map q)

/-- Every same original whole scalar composition map has its actual native projective weak left image over arbitrary
original bases. -/
theorem nativeStraightening_compositionScalar_projectiveWeakLeft (B : SSet.{u}) (K : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (((overParameterBifunctor (max B)).map (compositionCellOver r)).app K)) := by
  let _ := coherentDiagramModelCategory B
  intro F G q hq
  have hq' : Fibration q := (fibration_iff q).mpr hq
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (((overParameterBifunctor (max B)).map (compositionCellOver r)).app K) q).mpr
      (nativeUnstraightening_map_compositionScalarLifting B q K r hq')

/-- The actual original coherent target model makes every same native scalar composition image a trivial cofibration. -/
theorem nativeStraightening_compositionScalar_trivialCofibration (B : SSet.{u}) (K : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (((overParameterBifunctor (max B)).map (compositionCellOver r)).app K)) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeStraightening_compositionScalar_projectiveWeakLeft B K r

/-- The same original fixed-base composition marking cell is a mono on its unchanged whole slice carrier. -/
theorem compositionCellOver_nativeMono (B : SSet.{u}) (r : compositionCellTarget.{u} ⟶ max B) :
    Mono (compositionCellOver r) := by
  have : Mono (compositionCellOver r).left := compositionCell_mono
  exact Over.mono_of_mono_left _

/-- Every original whole fixed-base composition marking cell lifts the same native map of an actual coherent-model
fibration. -/
theorem nativeUnstraightening_map_originalCompositionLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ r : compositionCellTarget.{u} ⟶ max B,
      HasLiftingProperty (compositionCellOver r) ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq r
  let _ : HasLiftingProperty (compositionCellOver r).left ((nativeUnstraightening B).map q).left :=
    nativeUnstraightening_map_compositionLifting B q hq
  exact HasLiftingProperty.over _ ((nativeUnstraightening B).map q)

/-- The same original composition marking cell over every whole base simplex has its actual native projective weak
left image. -/
theorem nativeStraightening_originalComposition_projectiveWeakLeft (B : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (compositionCellOver r)) := by
  let _ := coherentDiagramModelCategory B
  intro F G q hq
  have hq' : Fibration q := (fibration_iff q).mpr hq
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff (compositionCellOver r) q).mpr
    (nativeUnstraightening_map_originalCompositionLifting B q hq' r)

/-- The same physical original composition marking cell has an actual native target-model trivial-cofibration image
over an arbitrary original base. -/
theorem nativeStraightening_originalComposition_trivialCofibration (B : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) ((nativeStraightening B).map (compositionCellOver r)) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeStraightening_originalComposition_projectiveWeakLeft B r

/-- Every same original composition-mark/maximal-scalar-mono corner has an actual native target trivial-cofibration
image from the original full pushout and both original side equations. -/
theorem nativeStraightening_compositionParameterCell_trivialCofibration (B : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (overParameterPushoutProduct a (compositionCellOver r))) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  let _ : Mono (compositionCellOver r) := compositionCellOver_nativeMono B r
  let i := compositionCellOver r
  let S := nativeStraightening B
  let s := overParameterPushout a i
  let _ : PreservesColimitsOfSize.{0, 0} S := (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  have hp := S.map_isPushout s.isPushout
  have hA := nativeStraightening_compositionScalar_trivialCofibration B A r
  have hD := nativeStraightening_compositionScalar_trivialCofibration B D r
  have hinr : trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) (S.map s.inr) :=
    MorphismProperty.of_isPushout hp.flip hA
  have hside : S.map s.inr ≫ S.map (overParameterPushoutProduct a i) =
      S.map (((overParameterBifunctor (max B)).map i).app D) :=
    nativeStraightening_parameterPushout_inr B a i
  have hcomp : weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ)
      (S.map s.inr ≫ S.map (overParameterPushoutProduct a i)) := hside.symm ▸ hD.2
  have hweak : weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ)
      (S.map (overParameterPushoutProduct a i)) :=
    MorphismProperty.of_precomp _ _ _ hinr.2 hcomp
  exact ⟨(cofibration_iff _).mp (nativeStraightening_parameterCell_cofibration B a i),
    hweak⟩

/-- The same whole original composition parameter corner has the actual projective weak left class in the original
target model. -/
theorem nativeStraightening_compositionParameterCell_projectiveWeakLeft (B : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (overParameterPushoutProduct a (compositionCellOver r))) := by
  let _ := coherentDiagramModelCategory B
  have h : trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (overParameterPushoutProduct a (compositionCellOver r))) :=
    nativeStraightening_compositionParameterCell_trivialCofibration B r a
  rw [coherentDiagramModel_trivialCofibrations B] at h
  exact h

/-- Every original marked evaluation coefficient of the same native composition parameter map is an actual
coefficient-model trivial cofibration. -/
theorem nativeStraightening_compositionParameterCell_evaluation_trivialCofibration (B : SSet.{u})
    (r : compositionCellTarget.{u} ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a]
    (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u}
      (((nativeStraightening B).map (overParameterPushoutProduct a (compositionCellOver r))).app x) := by
  let _ := coherentDiagramModelCategory B
  let _ : Mono (compositionCellOver r) := compositionCellOver_nativeMono B r
  have hc := nativeStraightening_parameterCell_evaluation_cofibration B a (compositionCellOver r) x
  have hw : coherentDiagramWeakEquivalences B
      ((nativeStraightening B).map (overParameterPushoutProduct a (compositionCellOver r))) :=
    coherentDiagramGeneratingWeakMonos_left_weak B _
      (nativeStraightening_compositionParameterCell_projectiveWeakLeft B r a)
  exact ⟨hc, (EvaluationTransfer.evaluationProperty_iff _ _ _).mp hw x⟩

/-- Both actual original models retain the same original composition-mark parameter corner and its same native
trivial-cofibration image. -/
theorem nativeStraightening_compositionParameterCell_bothModels (B : SSet.{u}) [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (Over (max B)) (overParameterPushoutProduct a (compositionCellOver r)) ∧
      trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
        ((nativeStraightening B).map (overParameterPushoutProduct a (compositionCellOver r))) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  have hs : cartesianTestingTrivialCofibrations B (compositionCellOver r) :=
    ⟨compositionCellOver_nativeMono B r, compositionCellOver_cartesian_weak r⟩
  exact ⟨cartesianWeakMono_parameter_closed (compositionCellOver r) hs a,
    nativeStraightening_compositionParameterCell_trivialCofibration B r a⟩

end SSet.Marked
