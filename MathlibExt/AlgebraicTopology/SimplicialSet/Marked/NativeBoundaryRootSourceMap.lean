/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryAllPairColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryFaceLegs

/-!
# The actual all-face native boundary source map

Every original full face chart enters the same supported root-boundary
chart. The genuine monomorphism of its attaching map detects equality
on every complete original face intersection. The actual marked
all-face colimit therefore constructs the entire native boundary
source map, retaining all original injections and its exact attaching
composite. Its inverse and full source isomorphism remain separate.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Both original full intersection maps have the same unchanged native face attaching composite. -/
theorem nativeBoundaryFaceChartSpan_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (p : (MultispanShape.prod (Fin (n + 2))).L) :
    (nativeBoundaryFaceChartSpan B n σ).fst p ≫
        nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.1}ᶜ) =
      (nativeBoundaryFaceChartSpan B n σ).snd p ≫
        nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.2}ᶜ) := by
  let d := nativeBoundaryFaceSubcomplexDiagram.{u} n
  let X := nativeSubcomplexBasisFunctor B (n + 1) σ
  let T := nativeStraightening B
  let a := d.multispanIndex.fst p
  let b := d.multispanIndex.snd p
  let g₁ := nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {p.1}ᶜ)
  let g₂ := nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {p.2}ᶜ)
  let e := (nativeSimplexImageIso B (n + 1) σ).hom
  have hx : X.map a ≫ g₁ = X.map b ≫ g₂ := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl
  have h₁ : T.map (X.map a) ≫ (T.map g₁ ≫ e) = T.map (X.map a ≫ g₁) ≫ e :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun v => v ≫ e) (T.map_comp (X.map a) g₁).symm)
  have h₂ : T.map (X.map b) ≫ (T.map g₂ ≫ e) = T.map (X.map b ≫ g₂) ≫ e :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun v => v ≫ e) (T.map_comp (X.map b) g₂).symm)
  exact h₁.trans ((congrArg (fun v => T.map v ≫ e) hx).trans h₂.symm)

/-- Every actual original full face intersection satisfies the same supported-boundary cocone relation. -/
theorem nativeBoundaryRootFace_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (p : (MultispanShape.prod (Fin (n + 2))).L) :
    (nativeBoundaryFaceChartSpan B n σ).fst p ≫ nativeBoundaryFaceToRoot B n σ p.1 =
      (nativeBoundaryFaceChartSpan B n σ).snd p ≫ nativeBoundaryFaceToRoot B n σ p.2 := by
  apply (cancel_mono (nativeRootBoundaryChartMap B (n + 1) σ)).mp
  let s := nativeBoundaryFaceChartSpan B n σ
  let r := nativeRootBoundaryChartMap B (n + 1) σ
  have h₁ : (s.fst p ≫ nativeBoundaryFaceToRoot B n σ p.1) ≫ r =
      s.fst p ≫ nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.1}ᶜ) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun v => s.fst p ≫ v) (nativeBoundaryFaceToRoot_attachment B n σ p.1))
  have h₂ : (s.snd p ≫ nativeBoundaryFaceToRoot B n σ p.2) ≫ r =
      s.snd p ≫ nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.2}ᶜ) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun v => s.snd p ≫ v) (nativeBoundaryFaceToRoot_attachment B n σ p.2))
  exact h₁.trans ((nativeBoundaryFaceChartSpan_attachment B n σ p).trans h₂.symm)

/-- All original full boundary face charts and intersections give the actual cocone into the same native supported
root-boundary chart. -/
def nativeBoundaryRootFaceCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    Multicofork (nativeBoundaryFaceChartSpan B n σ) :=
  Multicofork.ofπ _ (nativeRootBoundaryChart B (n + 1) σ)
    (nativeBoundaryFaceToRoot B n σ) (nativeBoundaryRootFace_condition B n σ)

/-- The actual native all-face boundary colimit maps to the unchanged complete supported chart through its genuine
whole marked colimit descent. -/
def nativeBoundaryRootSourceMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)) ⟶ nativeRootBoundaryChart B (n + 1) σ :=
  (nativeBoundaryFaceChartIsColimit B n σ).desc (nativeBoundaryRootFaceCocone B n σ)

/-- Every original full native boundary face injection retains precisely its same supported face leg under the
constructed whole source map. -/
theorem nativeBoundaryRootSourceMap_leg (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    (nativeBoundaryFaceChartCocone B n σ).π i ≫ nativeBoundaryRootSourceMap B n σ =
      nativeBoundaryFaceToRoot B n σ i :=
  (nativeBoundaryFaceChartIsColimit B n σ).fac (nativeBoundaryRootFaceCocone B n σ) (.right i)

/-- The same original whole native boundary face injection retains its unchanged original simplex attaching map. -/
theorem nativeBoundaryFaceChartCocone_attachment (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    (nativeBoundaryFaceChartCocone B n σ).π i ≫ nativeBoundaryChartMap B (n + 1) σ =
      nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) := by
  let d := nativeBoundaryFaceSubcomplexDiagram.{u} n
  let X := nativeSubcomplexBasisFunctor B (n + 1) σ
  let T := nativeStraightening B
  let a := d.multicofork.π i
  let g := nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1))
  let e := (nativeSimplexImageIso B (n + 1) σ).hom
  have hx : X.map a ≫ g = nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl
  have hm := (T.map_comp (X.map a) g).symm.trans (congrArg T.map hx)
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun v => v ≫ e) hm)

/-- The actual complete all-face source map preserves exactly the original whole native boundary attaching map. -/
theorem nativeBoundaryRootSourceMap_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeBoundaryRootSourceMap B n σ ≫ nativeRootBoundaryChartMap B (n + 1) σ =
      nativeBoundaryChartMap B (n + 1) σ := by
  apply Multicofork.IsColimit.hom_ext (nativeBoundaryFaceChartIsColimit B n σ)
  intro i
  have h₁ : (nativeBoundaryFaceChartCocone B n σ).π i ≫
      (nativeBoundaryRootSourceMap B n σ ≫ nativeRootBoundaryChartMap B (n + 1) σ) =
        nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun v => v ≫ nativeRootBoundaryChartMap B (n + 1) σ)
        (nativeBoundaryRootSourceMap_leg B n σ i)).trans (nativeBoundaryFaceToRoot_attachment B n σ i))
  exact h₁.trans (nativeBoundaryFaceChartCocone_attachment B n σ i).symm

/-- Every original restricted-simplex face chart enters the actual native boundary through its same whole
single-face unit comparison and original face injection. -/
def nativeBoundaryCofaceChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeSimplexChart B n (B.map (SimplexCategory.δ i).op σ) ⟶
      nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)) :=
  (nativeSingleFaceChartIso B n i σ).hom ≫ (nativeBoundaryFaceChartCocone B n σ).π i

/-- The actual all-face source map retains every original coface leg and its unchanged native unit mate. -/
theorem nativeBoundaryCofaceChartMap_root (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeBoundaryCofaceChartMap B n σ i ≫ nativeBoundaryRootSourceMap B n σ =
      nativeRootBoundaryCofaceMap B n σ i := by
  let e := nativeSingleFaceChartIso B n i σ
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => e.hom ≫ v) (nativeBoundaryRootSourceMap_leg B n σ i)).trans
      (e.hom_inv_id_assoc (nativeRootBoundaryCofaceMap B n σ i)))

end SSet.Marked
