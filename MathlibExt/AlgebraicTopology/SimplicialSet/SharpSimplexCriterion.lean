/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparisonSaturation
public import MathlibExt.AlgebraicTopology.SimplicialSet.RezkHornPreimage
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Simplex criterion for sharp maps

A map of simplicial sets is sharp exactly when its ordinary pullback comparison is a realization weak equivalence for every map from a standard simplex to the base and every simplex operator into that simplex. Horn preimage and saturation arguments extend these tests to arbitrary weak base changes.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen Simplicial

namespace SSet.SharpSaturation

/-- Rezk's FULL ordinary comparison condition: every n,m,b and every operator
into that SAME original b, including degree-zero simplex tests. -/
def allSimplexComparisons {X Y : SSet.{u}} (p : X ⟶ Y) : Prop :=
  ∀ (n m : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) (δ : ⦋m⦌ ⟶ ⦋n⦌),
    realizationWeakEquivalences (pullback.map p (SSet.stdSimplex.map δ ≫ b) p b
      (𝟙 X) (SSet.stdSimplex.map δ) (𝟙 Y) (by simp) (by simp))

/-- Native SOA plus actual horn9.3 and internally proved saturation give ALL
original anodyne comparisons, with no closure/generator/outcome hypothesis. -/
theorem anodyneExtensions_le_comparison_of_allSimplexComparisons
    {X Y : SSet.{u}} (p : X ⟶ Y) (h : allSimplexComparisons p) :
    anodyneExtensions ≤ comparisonTrivialCofibrations p := by
  have hs := comparisonTrivialCofibrations_saturated p
  let _ := hs.1
  let _ := hs.2.1
  let _ := hs.2.2.1
  let _ := hs.2.2.2
  rw [anodyneExtensions_eq_retracts_transfiniteCompositions]
  simp only [MorphismProperty.retracts_le_iff,
    MorphismProperty.transfiniteCompositions_le_iff,
    MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff,
    SSet.modelCategoryQuillen.J, iSup_le_iff, MorphismProperty.ofHoms_le_iff]
  intro n k
  refine ⟨anodyneExtensions.horn_ι k, fun b => ?_⟩
  exact RezkHornPreimage.horn_preimage_weak p (n + 1) k b (fun m δ => h (n + 1) m b δ)

private theorem trivialFibration_comparison_weak {X Y A B : SSet.{u}}
    (p : X ⟶ Y) (r : A ⟶ B) (t : B ⟶ Y)
    (hr : trivialFibrations SSet.{u} r) :
    realizationWeakEquivalences
      (pullback.map p (r ≫ t) p t (𝟙 X) r (𝟙 Y) (by simp) (by simp)) := by
  let e := pullbackLeftPullbackSndIso p t r
  have htf : trivialFibrations SSet.{u} (pullback.fst (pullback.snd p t) r) :=
    (trivialFibrations SSet.{u}).of_isPullback
      (IsPullback.of_hasPullback (pullback.snd p t) r).flip hr
  have hfac : e.hom ≫
      pullback.map p (r ≫ t) p t (𝟙 X) r (𝟙 Y) (by simp) (by simp) =
      pullback.fst (pullback.snd p t) r := by
    apply pullback.hom_ext
    · simp [e, pullback.map]
    · simp only [CategoryTheory.Category.assoc, pullback.map, pullback.lift_snd]
      change ((pullbackLeftPullbackSndIso p t r).hom ≫
          pullback.snd p (r ≫ t)) ≫ r =
        pullback.fst (pullback.snd p t) r ≫ pullback.snd p t
      exact (congrArg (fun k => k ≫ r)
        (pullbackLeftPullbackSndIso_hom_snd p t r)).trans
          (pullback.condition (f := pullback.snd p t) (g := r)).symm
  have h := htf.2
  rw [← hfac] at h
  exact (realizationWeakEquivalences.cancel_left_of_respectsIso _ _).mp h

private theorem allWeak_comparison {X Y U V : SSet.{u}} (p : X ⟶ Y)
    (h : allSimplexComparisons p) (w : U ⟶ V) (t : V ⟶ Y)
    (hw : realizationWeakEquivalences w) :
    realizationWeakEquivalences
      (pullback.map p (w ≫ t) p t (𝟙 X) w (𝟙 Y) (by simp) (by simp)) := by
  let d := MorphismProperty.factorizationData
    (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) w
  have hwr : realizationWeakEquivalences d.p := d.hp.2
  have hwi : realizationWeakEquivalences d.i := by
    apply realizationWeakEquivalences.of_postcomp d.i d.p hwr
    rwa [d.fac]
  have hi : anodyneExtensions d.i := by
    rw [anodyneExtensions_eq_trivialCofibrations]
    exact ⟨d.hi, hwi⟩
  have hci := (anodyneExtensions_le_comparison_of_allSimplexComparisons p h) d.i hi
  have hc₁ := hci.2 (d.p ≫ t)
  have hc₂ := trivialFibration_comparison_weak p d.p t d.hp
  have hc := realizationWeakEquivalences.comp_mem _ _ hc₁ hc₂
  have hcomp := pullback.map_comp
    (f := p) (g := d.i ≫ (d.p ≫ t))
    (f' := p) (g' := d.p ≫ t) (f'' := p) (g'' := t)
    (𝟙 X) (𝟙 X) d.i d.p (𝟙 Y) (𝟙 Y)
    (by simp) (by simp) (by simp) (by simp)
  simp only [Category.id_comp] at hcomp
  rw [hcomp] at hc
  have hg : d.i ≫ (d.p ≫ t) = w ≫ t :=
    (CategoryTheory.Category.assoc d.i d.p t).symm.trans
      (congrArg (fun k => k ≫ t) d.fac)
  let e := pullback.congrHom (f₁ := p) (f₂ := p) rfl hg
  let c := pullback.map p (w ≫ t) p t (𝟙 X) w (𝟙 Y) (by simp) (by simp)
  let oldc := pullback.map p (d.i ≫ (d.p ≫ t)) p t
    (𝟙 X) (d.i ≫ d.p) (𝟙 Y) (by simp) (by simp)
  have he : e.hom ≫ c = oldc := by
    apply pullback.hom_ext
    · simp [e, c, oldc, pullback.congrHom_hom, pullback.map]
    · simp [e, c, oldc, pullback.congrHom_hom, pullback.map, d.fac]
  have E : Arrow.mk oldc ≅ Arrow.mk c :=
    Arrow.isoMk e (Iso.refl _) (by
      change e.hom ≫ c = oldc ≫ 𝟙 (pullback p t)
      exact he.trans (CategoryTheory.Category.comp_id oldc).symm)
  exact (realizationWeakEquivalences.arrow_mk_iso_iff E).mp hc

private def simplexPointProductIso (n : ℕ) :
    (Δ[n] : SSet.{u}) ⨯ (Δ[0] : SSet.{u}) ≅ (Δ[n] : SSet.{u}) where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _)
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by simp

private theorem simplexToPoint_weak (n : ℕ) :
    realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) := by
  let e := simplexPointProductIso.{u} n
  have hp : realizationWeakEquivalences
      (prod.snd : (Δ[n] : SSet.{u}) ⨯ (Δ[0] : SSet.{u}) ⟶ _) :=
    stdSimplexProdSnd_mem_weakHomotopyEquivalences n (Δ[0] : SSet.{u})
  have h := realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso e.inv) hp
  have heq : e.inv ≫ prod.snd =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rwa [heq] at h

private theorem simplexOperator_weak {m n : ℕ} (δ : ⦋m⦌ ⟶ ⦋n⦌) :
    realizationWeakEquivalences (SSet.stdSimplex.{u}.map δ) := by
  apply realizationWeakEquivalences.of_postcomp (SSet.stdSimplex.map δ)
    (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) (simplexToPoint_weak n)
  have heq : SSet.stdSimplex.map δ ≫ SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[m] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [heq]
  exact simplexToPoint_weak m

/-- Original weak-base-change sharpness is equivalent to the FULL SAME-simplex
comparison condition for arbitrary original p, with no base Kan hypothesis. -/
theorem sharpBaseChange_iff_allSimplexComparisons {X Y : SSet.{u}} (p : X ⟶ Y) :
    SharpComparisonDraft.SharpBaseChange p ↔ allSimplexComparisons p := by
  constructor
  · intro h n m b δ
    have hδ : WeakEquivalence (SSet.stdSimplex.{u}.map δ) :=
      (HomotopicalAlgebra.weakEquivalence_iff _).2 (simplexOperator_weak δ)
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1
      (h _ _ (SSet.stdSimplex.map δ) b hδ)
  · intro h U V w t hw
    exact (HomotopicalAlgebra.weakEquivalence_iff _).2
      (allWeak_comparison p h w t ((HomotopicalAlgebra.weakEquivalence_iff _).1 hw))

/-- Rezk4.1/9.1 scalar simplex criterion for the actual comparison-based Sharp
predicate, retaining all original maps and every simplex operator. -/
theorem sharp_iff_allSimplexComparisons {X Y : SSet.{u}} (p : X ⟶ Y) :
    SharpComparisonDraft.Sharp p ↔ allSimplexComparisons p :=
  (SharpComparisonDraft.sharp_iff_baseChange p).trans
    (sharpBaseChange_iff_allSimplexComparisons p)

end SSet.SharpSaturation
