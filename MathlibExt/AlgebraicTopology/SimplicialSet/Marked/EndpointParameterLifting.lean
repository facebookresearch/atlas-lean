/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointPrismMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterTerminalComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetNaturality

/-!
# Full fixed-base marked endpoint parameter-boundary lifting

The original endpoint cell and its whole prescribed base edge are fixed
in the marked slice. The native relative prism ladder supplies every
parameter-boundary lift with the actual Cartesian or cocartesian
verticals. The original mixed triangles give all target prism markings.
The result concerns the complete native mapping restriction, including
every boundary degree, over an arbitrary quasicategory base.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

private def rightMinimalPointUnit (T : SSet.{u}) : prod (max T) (min (Δ[0] : SSet.{u})) ≅ max T :=
  prodSwapIso (max T) (min (Δ[0] : SSet.{u})) ≪≫ zeroParameterUnitIso .minimal (max T)

private def rightMinimalPointUnitUnderlying (T : SSet.{u}) : T ⊗ (Δ[0] : SSet.{u}) ≅ T :=
  forget.mapIso (rightMinimalPointUnit T)

private theorem minimalPoint_inv_eq_section (T : SSet.{u}) :
    (rightMinimalPointUnitUnderlying T).inv = prismSectionZero T := by
  apply CartesianMonoidalCategory.hom_ext
  · change 𝟙 T = prismSectionZero T ≫ CartesianMonoidalCategory.fst T (Δ[0] : SSet.{u})
    rw [← prismSectionAt_zero]
    exact (prismSectionAt_comp_fst T (0 : Fin 1)).symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem minimalPoint_native_graph (T : SSet.{u}) (ε : Fin 2) :
    (rightMinimalPointUnitUnderlying T).inv ≫ ((𝟙 T) ⊗ₘ stdSimplex.δ ε.rev) = prismSectionAt T ε := by
  rw [minimalPoint_inv_eq_section]
  fin_cases ε
  · exact prismSectionZero_whiskerLeft_δ_one T
  · exact prismSectionZero_whiskerLeft_δ_zero T

private theorem minimalPoint_endpoint_graph (T : SSet.{u}) (ε : Fin 2)
    (f : min (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}))
    (hf : f.hom = stdSimplex.δ ε.rev) :
    (rightMinimalPointUnitUnderlying T).inv ≫ (prodMap (𝟙 (max T)) f).hom = prismSectionAt T ε :=
  (congrArg (fun g => (rightMinimalPointUnitUnderlying T).inv ≫ ((𝟙 T) ⊗ₘ g)) hf).trans
    (minimalPoint_native_graph T ε)

private theorem minimalPoint_unit_natural {T T' : SSet.{u}} (a : T ⟶ T') :
    (rightMinimalPointUnitUnderlying T).inv ≫
        (prodMap (maximal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom =
      a ≫ (rightMinimalPointUnitUnderlying T').inv := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro j
    exact Fin.eq_zero _

/-- The actual Cartesian endpoint cell retains its original whole target-to-base edge. -/
def cartesianEndpointOver {B : SSet.{u}} (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    Over.mk (cartesianEndpointCell.{u} ≫ r) ⟶ Over.mk r :=
  Over.homMk cartesianEndpointCell rfl

/-- The dual cell keeps the original source endpoint and the same entire base edge. -/
def cocartesianEndpointOver {B : SSet.{u}} (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    Over.mk (cocartesianEndpointCell.{u} ≫ r) ⟶ Over.mk r :=
  Over.homMk cocartesianEndpointCell rfl

/-- Full original parameter-boundary squares lift against an intrinsic Cartesian target over the same actual
  base edge. -/
theorem cartesianEndpointOver_parameter_boundary_lifting {E B : SSet.{u}}
    (p : E ⟶ B) [CartesianFibration p] [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) (n : ℕ) :
    HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι (cartesianEndpointOver r))
      (Over.mkIdTerminal.from (Over.mk (cartesianProjection p))) := by
  let r₀ : (Δ[1] : SSet.{u}) ⟶ B := r.hom
  let a := (boundary.{u} n).ι
  let i := cartesianEndpointOver r
  let sq := overParameterPushout a i
  let target := Over.mk (cartesianProjection p)
  refine ⟨fun {top bottom} h => ?_⟩
  let Hmarked : prod (max (boundary.{u} n : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ cartesian p :=
    sq.inl.left ≫ top.left
  let cmarked : max (Δ[n] : SSet.{u}) ⟶ cartesian p :=
    (rightMinimalPointUnit (Δ[n] : SSet.{u})).inv ≫ sq.inr.left ≫ top.left
  let H : (boundary.{u} n : SSet.{u}) ⊗ Δ[1] ⟶ E := Hmarked.hom
  let c : (Δ[n] : SSet.{u}) ⟶ E := cmarked.hom
  let K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ B := (prodSnd (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u}))).hom ≫ r₀
  have hw : (prodMap (𝟙 (max (boundary.{u} n : SSet.{u}))) cartesianEndpointCell).hom ≫ H =
      (prodMap (maximal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom ≫
        (sq.inr.left ≫ top.left).hom := by
    exact congrArg Hom.hom (congrArg (fun f => f.left ≫ top.left) sq.isPushout.w)
  let uA : (boundary.{u} n : SSet.{u}) ⟶ (boundary.{u} n : SSet.{u}) ⊗ Δ[0] :=
    (rightMinimalPointUnitUnderlying (boundary.{u} n : SSet.{u})).inv
  let uD : (Δ[n] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[0] :=
    (rightMinimalPointUnitUnderlying (Δ[n] : SSet.{u})).inv
  let tA : (boundary.{u} n : SSet.{u}) ⊗ Δ[0] ⟶ (boundary.{u} n : SSet.{u}) ⊗ Δ[1] :=
    (prodMap (𝟙 (max (boundary.{u} n : SSet.{u}))) cartesianEndpointCell).hom
  let tD : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[1] :=
    (prodMap (𝟙 (max (Δ[n] : SSet.{u}))) cartesianEndpointCell).hom
  let tB : (boundary.{u} n : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[0] :=
    (prodMap (maximal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom
  let cD : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ E := (sq.inr.left ≫ top.left).hom
  have hgA : uA ≫ tA = prismSectionAt (boundary.{u} n : SSet.{u}) 1 :=
    minimalPoint_endpoint_graph _ 1 cartesianEndpointCell rfl
  have hgD : uD ≫ tD = prismSectionAt (Δ[n] : SSet.{u}) 1 :=
    minimalPoint_endpoint_graph _ 1 cartesianEndpointCell rfl
  have hn : uA ≫ tB = a ≫ uD := minimalPoint_unit_natural a
  have hHsrc : prismSectionAt (boundary.{u} n : SSet.{u}) 1 ≫ H = a ≫ c := by
    calc
      _ = (uA ≫ tA) ≫ H := congrArg (fun g => g ≫ H) hgA.symm
      _ = uA ≫ (tA ≫ H) := Category.assoc _ _ _
      _ = uA ≫ (tB ≫ cD) := congrArg (fun g => uA ≫ g) hw
      _ = (uA ≫ tB) ≫ cD := (Category.assoc _ _ _).symm
      _ = (a ≫ uD) ≫ cD := congrArg (fun g => g ≫ cD) hn
      _ = a ≫ c := Category.assoc _ _ _
  have hHbase : H ≫ p = (a ▷ (Δ[1] : SSet.{u})) ≫ K := by
    have hh := congrArg (fun f => f.hom) (Over.w (sq.inl ≫ top))
    exact hh
  have hcbase : c ≫ p = prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ K := by
    let π₀ : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[0] : SSet.{u}) :=
      (prodSnd (max (Δ[n] : SSet.{u})) (min (Δ[0] : SSet.{u}))).hom
    let π₁ : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ (Δ[1] : SSet.{u}) :=
      (prodSnd (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u}))).hom
    have hb : cD ≫ p = (π₀ ≫ cartesianEndpointCell.hom) ≫ r₀ :=
      congrArg Hom.hom (Over.w (sq.inr ≫ top))
    have ht : tD ≫ π₁ = π₀ ≫ cartesianEndpointCell.hom := rfl
    calc
      c ≫ p = uD ≫ (cD ≫ p) := Category.assoc _ _ _
      _ = uD ≫ ((π₀ ≫ cartesianEndpointCell.hom) ≫ r₀) := congrArg (fun g => uD ≫ g) hb
      _ = uD ≫ ((tD ≫ π₁) ≫ r₀) := congrArg (fun g => uD ≫ (g ≫ r₀)) ht.symm
      _ = (uD ≫ tD) ≫ (π₁ ≫ r₀) := by simp only [Category.assoc]
      _ = prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ K := congrArg (fun g => g ≫ K) hgD
  have hv : PrismOneVerticalsCartesian p H := by
    intro x
    exact Hmarked.preserve (show (verticalOneSimplex x) ∈
      (prod (max (boundary.{u} n : SSet.{u})) (max (Δ[1] : SSet.{u}))).marking from
      ⟨Set.mem_univ _, Set.mem_univ _⟩)
  obtain ⟨F, hFr, hFt, hFp, hFv⟩ := relativeCartesianPrismTgtExtension_boundary p n
    H c K hHsrc hcbase.symm hHbase hv
  let lmarked : prod (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ cartesian p :=
    markedCartesianPrismOfTarget p F hFv (by
      intro e _
      let e₀ : (Δ[n] : SSet.{u}) _⦋1⦌ := e
      have he : (prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ F).app (op ⦋1⦌) e₀ = c.app (op ⦋1⦌) e₀ :=
        congrArg (fun g => g.app (op ⦋1⦌) e₀) hFt
      exact (congrArg (fun z => CartesianEdge.IsPCartesian p (yonedaEquiv.symm z)) he).to_iff.mpr
        (cmarked.preserve (Set.mem_univ _)))
  let l : overParameter (max B) (Over.mk r) (Δ[n] : SSet.{u}) ⟶ target :=
    Over.homMk lmarked (Hom.ext hFp)
  refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
  · apply sq.isPushout.hom_ext
    · apply Over.OverMorphism.ext
      apply Hom.ext
      change (sq.inl.left.hom ≫ (overParameterPushoutProduct a i).left.hom) ≫ F = H
      exact (congrArg (fun f => f.left.hom ≫ F) sq.inl_ι).trans hFr
    · apply Over.OverMorphism.ext
      apply Hom.ext
      apply (cancel_epi (rightMinimalPointUnitUnderlying (Δ[n] : SSet.{u})).inv).mp
      have ht : sq.inr.left.hom ≫ (overParameterPushoutProduct a i).left.hom = tD :=
        congrArg (fun f => f.left.hom) sq.inr_ι
      change uD ≫ ((sq.inr.left.hom ≫ (overParameterPushoutProduct a i).left.hom) ≫ F) = c
      exact (congrArg (fun g => uD ≫ (g ≫ F)) ht).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (fun g => g ≫ F) hgD).trans hFt))
  · exact Over.mkIdTerminal.hom_ext _ _

/-- Full original parameter-boundary squares lift against an intrinsic Cocartesian target over the same
  actual base edge. -/
theorem cocartesianEndpointOver_parameter_boundary_lifting {E B : SSet.{u}}
    (p : E ⟶ B) [CocartesianFibration p] [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) (n : ℕ) :
    HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι (cocartesianEndpointOver r))
      (Over.mkIdTerminal.from (Over.mk (cocartesianProjection p))) := by
  let r₀ : (Δ[1] : SSet.{u}) ⟶ B := r.hom
  let a := (boundary.{u} n).ι
  let i := cocartesianEndpointOver r
  let sq := overParameterPushout a i
  let target := Over.mk (cocartesianProjection p)
  refine ⟨fun {top bottom} h => ?_⟩
  let Hmarked : prod (max (boundary.{u} n : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ cocartesian p :=
    sq.inl.left ≫ top.left
  let cmarked : max (Δ[n] : SSet.{u}) ⟶ cocartesian p :=
    (rightMinimalPointUnit (Δ[n] : SSet.{u})).inv ≫ sq.inr.left ≫ top.left
  let H : (boundary.{u} n : SSet.{u}) ⊗ Δ[1] ⟶ E := Hmarked.hom
  let c : (Δ[n] : SSet.{u}) ⟶ E := cmarked.hom
  let K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ B := (prodSnd (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u}))).hom ≫ r₀
  have hw : (prodMap (𝟙 (max (boundary.{u} n : SSet.{u}))) cocartesianEndpointCell).hom ≫ H =
      (prodMap (maximal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom ≫
        (sq.inr.left ≫ top.left).hom := by
    exact congrArg Hom.hom (congrArg (fun f => f.left ≫ top.left) sq.isPushout.w)
  let uA : (boundary.{u} n : SSet.{u}) ⟶ (boundary.{u} n : SSet.{u}) ⊗ Δ[0] :=
    (rightMinimalPointUnitUnderlying (boundary.{u} n : SSet.{u})).inv
  let uD : (Δ[n] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[0] :=
    (rightMinimalPointUnitUnderlying (Δ[n] : SSet.{u})).inv
  let tA : (boundary.{u} n : SSet.{u}) ⊗ Δ[0] ⟶ (boundary.{u} n : SSet.{u}) ⊗ Δ[1] :=
    (prodMap (𝟙 (max (boundary.{u} n : SSet.{u}))) cocartesianEndpointCell).hom
  let tD : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[1] :=
    (prodMap (𝟙 (max (Δ[n] : SSet.{u}))) cocartesianEndpointCell).hom
  let tB : (boundary.{u} n : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[0] :=
    (prodMap (maximal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom
  let cD : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ E := (sq.inr.left ≫ top.left).hom
  have hgA : uA ≫ tA = prismSectionAt (boundary.{u} n : SSet.{u}) 0 :=
    minimalPoint_endpoint_graph _ 0 cocartesianEndpointCell rfl
  have hgD : uD ≫ tD = prismSectionAt (Δ[n] : SSet.{u}) 0 :=
    minimalPoint_endpoint_graph _ 0 cocartesianEndpointCell rfl
  have hn : uA ≫ tB = a ≫ uD := minimalPoint_unit_natural a
  have hHsrc : prismSectionAt (boundary.{u} n : SSet.{u}) 0 ≫ H = a ≫ c := by
    calc
      _ = (uA ≫ tA) ≫ H := congrArg (fun g => g ≫ H) hgA.symm
      _ = uA ≫ (tA ≫ H) := Category.assoc _ _ _
      _ = uA ≫ (tB ≫ cD) := congrArg (fun g => uA ≫ g) hw
      _ = (uA ≫ tB) ≫ cD := (Category.assoc _ _ _).symm
      _ = (a ≫ uD) ≫ cD := congrArg (fun g => g ≫ cD) hn
      _ = a ≫ c := Category.assoc _ _ _
  have hHbase : H ≫ p = (a ▷ (Δ[1] : SSet.{u})) ≫ K := by
    have hh := congrArg (fun f => f.hom) (Over.w (sq.inl ≫ top))
    exact hh
  have hcbase : c ≫ p = prismSectionAt (Δ[n] : SSet.{u}) 0 ≫ K := by
    let π₀ : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[0] : SSet.{u}) :=
      (prodSnd (max (Δ[n] : SSet.{u})) (min (Δ[0] : SSet.{u}))).hom
    let π₁ : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ (Δ[1] : SSet.{u}) :=
      (prodSnd (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u}))).hom
    have hb : cD ≫ p = (π₀ ≫ cocartesianEndpointCell.hom) ≫ r₀ :=
      congrArg Hom.hom (Over.w (sq.inr ≫ top))
    have ht : tD ≫ π₁ = π₀ ≫ cocartesianEndpointCell.hom := rfl
    calc
      c ≫ p = uD ≫ (cD ≫ p) := Category.assoc _ _ _
      _ = uD ≫ ((π₀ ≫ cocartesianEndpointCell.hom) ≫ r₀) := congrArg (fun g => uD ≫ g) hb
      _ = uD ≫ ((tD ≫ π₁) ≫ r₀) := congrArg (fun g => uD ≫ (g ≫ r₀)) ht.symm
      _ = (uD ≫ tD) ≫ (π₁ ≫ r₀) := by simp only [Category.assoc]
      _ = prismSectionAt (Δ[n] : SSet.{u}) 0 ≫ K := congrArg (fun g => g ≫ K) hgD
  have hv : PrismOneVerticalsCocartesian p H := by
    intro x
    exact Hmarked.preserve (show (verticalOneSimplex x) ∈
      (prod (max (boundary.{u} n : SSet.{u})) (max (Δ[1] : SSet.{u}))).marking from
      ⟨Set.mem_univ _, Set.mem_univ _⟩)
  obtain ⟨F, hFr, hFt, hFp, hFv⟩ := relativeCocartesianPrismSrcExtension_boundary p n
    H c K hHsrc hcbase.symm hHbase hv
  let lmarked : prod (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ cocartesian p :=
    markedCocartesianPrismOfSource p F hFv (by
      intro e _
      let e₀ : (Δ[n] : SSet.{u}) _⦋1⦌ := e
      have he : (prismSectionAt (Δ[n] : SSet.{u}) 0 ≫ F).app (op ⦋1⦌) e₀ = c.app (op ⦋1⦌) e₀ :=
        congrArg (fun g => g.app (op ⦋1⦌) e₀) hFt
      exact (congrArg (fun z => CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm z)) he).to_iff.mpr
        (cmarked.preserve (Set.mem_univ _)))
  let l : overParameter (max B) (Over.mk r) (Δ[n] : SSet.{u}) ⟶ target :=
    Over.homMk lmarked (Hom.ext hFp)
  refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
  · apply sq.isPushout.hom_ext
    · apply Over.OverMorphism.ext
      apply Hom.ext
      change (sq.inl.left.hom ≫ (overParameterPushoutProduct a i).left.hom) ≫ F = H
      exact (congrArg (fun f => f.left.hom ≫ F) sq.inl_ι).trans hFr
    · apply Over.OverMorphism.ext
      apply Hom.ext
      apply (cancel_epi (rightMinimalPointUnitUnderlying (Δ[n] : SSet.{u})).inv).mp
      have ht : sq.inr.left.hom ≫ (overParameterPushoutProduct a i).left.hom = tD :=
        congrArg (fun f => f.left.hom) sq.inr_ι
      change uD ≫ ((sq.inr.left.hom ≫ (overParameterPushoutProduct a i).left.hom) ≫ F) = c
      exact (congrArg (fun g => uD ≫ (g ≫ F)) ht).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (fun g => g ≫ F) hgD).trans hFt))
  · exact Over.mkIdTerminal.hom_ext _ _

/-- Every complete original Cartesian endpoint restriction has all scalar boundary lifts into its canonical
  intrinsic target. -/
theorem cartesianEndpointOver_canonical_mapping_rlp {E B : SSet.{u}}
    (p : E ⟶ B) [CartesianFibration p] [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map (cartesianEndpointOver r).op) := by
  apply (overParameterBoundary_terminal_lifting_iff _ _).mp
  exact cartesianEndpointOver_parameter_boundary_lifting p r

/-- The whole original dual source-endpoint restriction has its native canonical mapping-boundary right class. -/
theorem cocartesianEndpointOver_canonical_mapping_rlp {E B : SSet.{u}}
    (p : E ⟶ B) [CocartesianFibration p] [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map
        (cocartesianEndpointOver r).op) := by
  apply (overParameterBoundary_terminal_lifting_iff _ _).mp
  exact cocartesianEndpointOver_parameter_boundary_lifting p r

/-- Actual Cartesian targets with their supplied original marking retain all whole endpoint mapping-boundary lifts. -/
theorem cartesianEndpointOver_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) (target : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) target.obj).map
      (cartesianEndpointOver r).op) := by
  let p : target.obj.left.toSSet ⟶ B := target.obj.hom.hom
  let _ : CartesianFibration p := target.property.1
  let e : target.obj ≅ Over.mk (cartesianProjection p) :=
    Over.isoMk (cartesianMarkingIso p target.property.2) (Hom.ext rfl)
  let s := overMappingRestrictionTargetIso .maximal (cartesianEndpointOver r) e
  exact (modelCategoryQuillen.I.rlp.arrow_mk_iso_iff s).mpr
    (cartesianEndpointOver_canonical_mapping_rlp p r)

/-- The same exact target-marking transport keeps all native dual source-endpoint boundary lifts. -/
theorem cocartesianEndpointOver_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) (target : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) target.obj).map
      (cocartesianEndpointOver r).op) := by
  let p : target.obj.left.toSSet ⟶ B := target.obj.hom.hom
  let _ : CocartesianFibration p := target.property.1
  let e : target.obj ≅ Over.mk (cocartesianProjection p) :=
    Over.isoMk (cocartesianMarkingIso p target.property.2) (Hom.ext rfl)
  let s := overMappingRestrictionTargetIso .maximal (cocartesianEndpointOver r) e
  exact (modelCategoryQuillen.I.rlp.arrow_mk_iso_iff s).mpr
    (cocartesianEndpointOver_canonical_mapping_rlp p r)

/-- Every original Cartesian endpoint over its whole original base edge is genuinely mapping weak. -/
theorem cartesianEndpointOver_weak {B : SSet.{u}} [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) : cartesianWeakEquivalences B (cartesianEndpointOver r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro target
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (cartesianEndpointOver_mapping_rlp r target)

/-- The full original cocartesian source endpoint has the genuine dual mapping weakness. -/
theorem cocartesianEndpointOver_weak {B : SSet.{u}} [Quasicategory B]
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) : cocartesianWeakEquivalences B (cocartesianEndpointOver r) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro target
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (cocartesianEndpointOver_mapping_rlp r target)

end SSet.Marked
