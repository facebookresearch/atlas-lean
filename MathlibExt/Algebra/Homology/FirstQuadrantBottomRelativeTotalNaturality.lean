/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence

/-!
# Naturality of the finite bottom-relative-to-total comparison

For a morphism f:K→L of first-quadrant bicomplexes in an abelian category, put m=p+q and
u=p+q+1. The finite upper stage G_u contains the three-term window computing H_m of the total
complex. The bottom-relative stage comparison followed by the upper-stage-to-total comparison
gives e_K:H^{-m}_K(⊥,u)≅H_m(Tot K).

The relative spectral map induced by f, evaluated at ⊥→u in degree -m, commutes with e_K,e_L and
H_m(Tot f). This naturality combines the complete-stage map with the map of the total
complexes, with arbitrary object and morphism universes.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category in arbitrary universes, K,L bicomplexes of shape (down ℕ,down ℕ),
f:K→L and p,q : ℕ. Put m=p+q, ℓ=(p:ℤ)−1 and u=m+1; Hᵃ(s,t) denotes relative cochain homology of
the complete horizontal filtration. Let h_f:H^{-m}_K(⊥,u)→H^{-m}_L(⊥,u) be the complete
spectral-object map and e_K,e_L the bottom-relative-to-total isomorphisms. Then
h_f≫e_L.hom=e_K.hom≫H_m(total.map(f)), where the total shape is down ℕ and the target degree is
m. -/
theorem horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (p + q) := by
  let n : ℕ := p + q
  let I : EInt := horizontalAbutmentUpperIndex p q
  let m : horizontalCompleteFilteredTotalComplex K I ⟶
      horizontalCompleteFilteredTotalComplex L I :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f I
  let uK : horizontalCompleteFilteredTotalComplex K I ⟶ K.total (ComplexShape.down ℕ) :=
    horizontalCompleteFilteredTotalToTotal K I
  let uL : horizontalCompleteFilteredTotalComplex L I ⟶ L.total (ComplexShape.down ℕ) :=
    horizontalCompleteFilteredTotalToTotal L I
  let t : K.total (ComplexShape.down ℕ) ⟶ L.total (ComplexShape.down ℕ) :=
    total.map f (ComplexShape.down ℕ)
  have hbottom : horizontalBottomToStageMap I = horizontalCanonicalAbutmentTotalMap p q :=
    Subsingleton.elim _ _
  have hstage : ((horizontalCompleteFiltrationSpectralObjectMap f).hom (-(n : ℤ))).app
        (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyStageIso L I n).hom =
      (horizontalBottomRelativeHomologyStageIso K I n).hom ≫
        HomologicalComplex.homologyMap m n := by
    have hs := horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex f I n
    rw [hbottom] at hs
    exact hs
  have hchain : m ≫ uL = uK ≫ t :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f I
  have htotal : HomologicalComplex.homologyMap m n ≫
        HomologicalComplex.homologyMap uL n =
      HomologicalComplex.homologyMap uK n ≫ HomologicalComplex.homologyMap t n := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun g : horizontalCompleteFilteredTotalComplex K I ⟶
          L.total (ComplexShape.down ℕ) => HomologicalComplex.homologyMap g n) hchain
  have huK : (horizontalAbutmentUpperHomologyToTotalIso K p q).hom =
      HomologicalComplex.homologyMap uK n := by
    change horizontalCompleteHomologyToTotal K n I = HomologicalComplex.homologyMap uK n
    exact horizontalCompleteHomologyToTotal_eq K n I
  have huL : (horizontalAbutmentUpperHomologyToTotalIso L p q).hom =
      HomologicalComplex.homologyMap uL n := by
    change horizontalCompleteHomologyToTotal L n I = HomologicalComplex.homologyMap uL n
    exact horizontalCompleteHomologyToTotal_eq L n I
  simp only [horizontalBottomRelativeHomologyToTotalIso, Iso.trans_hom]
  rw [huK, huL]
  change ((horizontalCompleteFiltrationSpectralObjectMap f).hom (-(n : ℤ))).app
      (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyStageIso L I n).hom ≫
        HomologicalComplex.homologyMap uL n =
    ((horizontalBottomRelativeHomologyStageIso K I n).hom ≫
      HomologicalComplex.homologyMap uK n) ≫ HomologicalComplex.homologyMap t n
  calc
    _ = (horizontalBottomRelativeHomologyStageIso K I n).hom ≫
        HomologicalComplex.homologyMap m n ≫ HomologicalComplex.homologyMap uL n := by
      simpa only [Category.assoc] using hstage =≫ HomologicalComplex.homologyMap uL n
    _ = _ := by
      simpa only [Category.assoc] using
        (horizontalBottomRelativeHomologyStageIso K I n).hom ≫= htotal

end HomologicalComplex₂

end
