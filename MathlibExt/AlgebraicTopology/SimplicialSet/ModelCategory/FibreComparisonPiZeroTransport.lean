/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original fibre comparisons and transport between base vertices via pi0.
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Transport of fibre comparison weakness along components

For a comparison commuting with two Kan–Quillen fibrations over the same base, the induced point-pullback comparison is a realization weak equivalence at one base vertex exactly when it is weak at a vertex in the same connected component. The transport retains the literal comparison and its total-space and base projections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- The original comparison pulled back to one specified base map. -/
def sameBasePullbackComparison {E D B T : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : T ⟶ B) : pullback s b ⟶ pullback t b :=
  pullback.map s b t b c (𝟙 T) (𝟙 B)
    (by simpa only [Category.comp_id] using h.symm)
    (by simp only [Category.comp_id, Category.id_comp])

/-- The comparison preserves the original total-space projection. -/
@[reassoc]
theorem sameBasePullbackComparison_fst {E D B T : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : T ⟶ B) :
    sameBasePullbackComparison c s t h b ≫ pullback.fst t b =
      pullback.fst s b ≫ c :=
  pullback.lift_fst _ _ _

/-- The same map preserves the full chosen base leg, including a simplicial point. -/
@[reassoc]
theorem sameBasePullbackComparison_snd {E D B T : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : T ⟶ B) :
    sameBasePullbackComparison c s t h b ≫ pullback.snd t b =
      pullback.snd s b := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private def baseChangeInclusion {E B T U : SSet.{u}}
    (s : E ⟶ B) (b : U ⟶ B) (i : T ⟶ U) :
    pullback s (i ≫ b) ⟶ pullback s b :=
  pullback.map s (i ≫ b) s b (𝟙 E) i (𝟙 B)
    (by simp only [Category.comp_id, Category.id_comp])
    (by simp only [Category.comp_id])

@[reassoc]
private theorem baseChangeInclusion_fst {E B T U : SSet.{u}}
    (s : E ⟶ B) (b : U ⟶ B) (i : T ⟶ U) :
    baseChangeInclusion s b i ≫ pullback.fst s b =
      pullback.fst s (i ≫ b) := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
private theorem baseChangeInclusion_snd {E B T U : SSet.{u}}
    (s : E ⟶ B) (b : U ⟶ B) (i : T ⟶ U) :
    baseChangeInclusion s b i ≫ pullback.snd s b =
      pullback.snd s (i ≫ b) ≫ i :=
  pullback.lift_snd _ _ _

private theorem baseChangeInclusion_isPullback {E B T U : SSet.{u}}
    (s : E ⟶ B) (b : U ⟶ B) (i : T ⟶ U) :
    IsPullback (pullback.snd s (i ≫ b))
      (baseChangeInclusion s b i) i (pullback.snd s b) := by
  have outer : IsPullback
      (baseChangeInclusion s b i ≫ pullback.fst s b)
      (pullback.snd s (i ≫ b)) s (i ≫ b) := by
    rw [baseChangeInclusion_fst]
    exact IsPullback.of_hasPullback s (i ≫ b)
  exact (IsPullback.of_right outer
    (baseChangeInclusion_snd s b i) (IsPullback.of_hasPullback s b)).flip

private theorem baseChangeInclusion_weak {E B T U : SSet.{u}}
    (s : E ⟶ B) (b : U ⟶ B) (i : T ⟶ U)
    [Fibration s] (hi : realizationWeakEquivalences i) :
    realizationWeakEquivalences (baseChangeInclusion s b i) := by
  let : Fibration (pullback.snd s b) := inferInstance
  let : WeakEquivalence i := (weakEquivalence_iff i).mpr hi
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback
      (baseChangeInclusion_isPullback s b i))

private theorem sameBasePullbackComparison_baseChange {E D B T U : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : U ⟶ B) (i : T ⟶ U) :
    sameBasePullbackComparison c s t h (i ≫ b) ≫ baseChangeInclusion t b i =
      baseChangeInclusion s b i ≫ sameBasePullbackComparison c s t h b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeInclusion_fst,
      sameBasePullbackComparison_fst, baseChangeInclusion_fst_assoc]
  · simp only [Category.assoc, baseChangeInclusion_snd,
      sameBasePullbackComparison_snd, sameBasePullbackComparison_snd_assoc]

private theorem sameBasePullbackComparison_weak_iff_baseChange
    {E D B T U : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : U ⟶ B) (i : T ⟶ U) [Fibration s] [Fibration t]
    (hi : realizationWeakEquivalences i) :
    realizationWeakEquivalences (sameBasePullbackComparison c s t h (i ≫ b)) ↔
      realizationWeakEquivalences (sameBasePullbackComparison c s t h b) := by
  have hs := baseChangeInclusion_weak s b i hi
  have ht := baseChangeInclusion_weak t b i hi
  have square := sameBasePullbackComparison_baseChange c s t h b i
  constructor
  · intro hc
    have composite := realizationWeakEquivalences.comp_mem _ _ hc ht
    rw [square] at composite
    exact realizationWeakEquivalences.of_precomp _ _ hs composite
  · intro hc
    have composite := realizationWeakEquivalences.comp_mem _ _ hs hc
    rw [← square] at composite
    exact realizationWeakEquivalences.of_postcomp _ _ ht composite

private theorem endpointDeltaOne_weak (i : Fin 2) :
    realizationWeakEquivalences (stdSimplex.δ i :
      (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u})) := by
  have nerve_weak :=
    NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_hasTerminal
      (C := ULift.{u} (Fin 2))
  have simplex_weak := MorphismProperty.RespectsIso.precomp realizationWeakEquivalences
    (stdSimplex.isoNerve 1).hom _ nerve_weak
  have terminal_weak : realizationWeakEquivalences
      (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) := by
    rwa [show (stdSimplex.isoNerve 1).hom ≫
        stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin 2))) =
        stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) from stdSimplex.ext₀]
      at simplex_weak
  apply realizationWeakEquivalences.of_postcomp _ _ terminal_weak
  have fac : stdSimplex.δ i ≫ stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) =
      𝟙 (Δ[0] : SSet.{u}) := stdSimplex.ext₀
  rw [fac]
  exact realizationWeakEquivalences.id_mem _

/-- Weakness of the original comparison fibre is invariant across a specified base edge.
The comparison itself has no fibration hypothesis. -/
theorem sameBasePullbackComparison_weak_iff_of_edge
    {E D B : SSet.{u}} (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B)
    (h : c ≫ t = s) [Fibration s] [Fibration t]
    {x y : B _⦋0⦌} (e : B.Edge x y) :
    realizationWeakEquivalences
      (sameBasePullbackComparison c s t h (yonedaEquiv.symm x)) ↔
    realizationWeakEquivalences
      (sameBasePullbackComparison c s t h (yonedaEquiv.symm y)) := by
  let b : (Δ[1] : SSet.{u}) ⟶ B := yonedaEquiv.symm e.edge
  have first := sameBasePullbackComparison_weak_iff_baseChange c s t h b
    (stdSimplex.δ (1 : Fin 2)) (endpointDeltaOne_weak 1)
  have last := sameBasePullbackComparison_weak_iff_baseChange c s t h b
    (stdSimplex.δ (0 : Fin 2)) (endpointDeltaOne_weak 0)
  have first_eq : stdSimplex.δ (1 : Fin 2) ≫ b = yonedaEquiv.symm x :=
    e.δ_one_yonedaEquiv_symm
  have last_eq : stdSimplex.δ (0 : Fin 2) ≫ b = yonedaEquiv.symm y :=
    e.δ_zero_yonedaEquiv_symm
  rw [first_eq] at first
  rw [last_eq] at last
  exact first.trans last.symm

/-- Component coverage extends fibre weakness for a comparison between two fibrations.
Both original point pullbacks and their base legs are retained, including an empty base. -/
theorem sameBasePullbackComparison_weak_iff_of_piZero_eq
    {E D B : SSet.{u}} (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B)
    (h : c ≫ t = s) [Fibration s] [Fibration t]
    (x y : B _⦋0⦌) (hxy : π₀.mk x = π₀.mk y) :
    realizationWeakEquivalences
      (sameBasePullbackComparison c s t h (yonedaEquiv.symm x)) ↔
    realizationWeakEquivalences
      (sameBasePullbackComparison c s t h (yonedaEquiv.symm y)) := by
  have connected : Relation.EqvGen π₀Rel x y := (π₀.mk_eq_mk_iff x y).mp hxy
  clear hxy
  induction connected with
  | rel x y hrel =>
      obtain ⟨e⟩ := hrel
      exact sameBasePullbackComparison_weak_iff_of_edge c s t h e
  | refl x => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end SSet
