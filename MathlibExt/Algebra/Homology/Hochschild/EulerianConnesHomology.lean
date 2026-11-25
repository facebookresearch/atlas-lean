/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricRegularConnesHomology
public import MathlibExt.Algebra.Homology.Hochschild.EulerianConnesWeights
public import MathlibExt.Algebra.Homology.Hochschild.NormalizedEulerianHodge

/-!
# Eulerian weights of the Connes homology map

Regular normalized Connes B induces a degree-one homology
map. Its Eulerian intertwining relation sends weight i
to weight i + 1 on the Hodge homology objects. The
projectors require a rational ground algebra; no
algebra or coefficient flatness is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]

/-- The Eulerian component identity gives the all-degree B shift on original Hodge homology. -/
@[reassoc]
theorem normalizedEulerianHomology_connes_shift (n i : ℕ) :
    normalizedEulerianHomologyProjector k A A n i ≫ regularNormalizedConnesHomology k A n =
      regularNormalizedConnesHomology k A n ≫ normalizedEulerianHomologyProjector k A A (n + 1) (i + 1) := by
  let H := regularNormalizedBoundaryHomotopy k A
  have hComponent : (normalizedEulerianChainMap k A A i).f n ≫ H.hom n (n + 1) =
      H.hom n (n + 1) ≫ (normalizedEulerianChainMap k A A (i + 1)).f (n + 1) := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, normalizedEulerianChainMap_f, H,
      regularNormalizedBoundaryHomotopy_hom, regularNormalizedConnes_hom]
    rw [normalizedConnesBoundary_eq_formula]
    change (normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i) =
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp (normalizedConnesFormula k A n)
    have hs := normalizedEulerian_connes_shift k A n i
    rw [normalizedConnesBoundary_eq_formula] at hs
    change (normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i) =
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp (normalizedConnesFormula k A n) at hs
    exact hs
  exact H.homologyDegreeMap_naturality_square
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) H
      (normalizedEulerianChainMap k A A i) (normalizedEulerianChainMap k A A (i + 1)) hComponent

/-- The output weight zero annihilates native regular Connes homology in every original degree. -/
theorem normalizedEulerianHomology_connes_zero_weight (n : ℕ) :
    regularNormalizedConnesHomology k A n ≫ normalizedEulerianHomologyProjector k A A (n + 1) 0 = 0 := by
  let H := regularNormalizedBoundaryHomotopy k A
  have hComponent : (0 : normalizedChainComplex k A A ⟶ normalizedChainComplex k A A).f n ≫
      H.hom n (n + 1) = H.hom n (n + 1) ≫ (normalizedEulerianChainMap k A A 0).f (n + 1) := by
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.zero_f, ModuleCat.hom_comp, ModuleCat.hom_zero,
      normalizedEulerianChainMap_f, H,
      regularNormalizedBoundaryHomotopy_hom, regularNormalizedConnes_hom]
    rw [normalizedConnesBoundary_eq_formula]
    change (normalizedConnesFormula k A n).comp
        (0 : Module.End k (A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A))) =
      (normalizedEulerianOperator k A A (n + 1) 0).comp (normalizedConnesFormula k A n)
    rw [LinearMap.comp_zero]
    have hz := normalizedEulerian_connes_zero_weight k A n
    rw [normalizedConnesBoundary_eq_formula] at hz
    change (normalizedEulerianOperator k A A (n + 1) 0).comp (normalizedConnesFormula k A n) = 0 at hz
    exact hz.symm
  have h := H.homologyDegreeMap_naturality_square
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) H
      (0 : normalizedChainComplex k A A ⟶ normalizedChainComplex k A A)
        (normalizedEulerianChainMap k A A 0) hComponent
  simpa only [HomologicalComplex.homologyMap_zero, zero_comp,
    normalizedEulerianHomologyProjector, regularNormalizedConnesHomology, H] using h.symm

end ModuleCat.Algebra.Hochschild.Symmetric
