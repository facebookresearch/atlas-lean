/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Source proposal; Native elaboration is unexecuted. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricRegularNormalized
public import MathlibExt.Algebra.Homology.HomologicalComplex.ConcreteHomotopyClass

/-!
# Regular normalized Connes maps on homology

For regular coefficients, the normalized Connes homotopy
induces a degree-one homology map with its cycle formula
and square-zero law. The construction uses the regular
coefficient complex over an arbitrary commutative ground ring.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-- The regular Connes homotopy on the symmetric normalized endpoints. -/
def regularNormalizedBoundaryHomotopy :
    Homotopy (0 : normalizedChainComplex k A A ⟶ normalizedChainComplex k A A) 0 := by
  let e := regularNormalizedComplexIso k A
  let H := ((NonUnital.normalizedBoundaryHomotopy k A).compLeft e.hom).compRight e.inv
  refine { hom := H.hom, zero := H.zero, comm := ?_ }
  intro n
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply,
    Limits.comp_zero, Limits.zero_comp] using H.comm n

/-- The original normalized B is retained as the adjacent component. -/
theorem regularNormalizedBoundaryHomotopy_hom (n : ℕ) :
    (regularNormalizedBoundaryHomotopy k A).hom n (n + 1) = regularNormalizedConnes k A n := by
  have hComponent :
      (regularNormalizedBoundaryHomotopy k A).hom n (n + 1) =
        ((regularNormalizedComplexIso k A).hom.f n ≫
          (NonUnital.normalizedBoundaryHomotopy k A).hom n (n + 1)) ≫
            (regularNormalizedComplexIso k A).inv.f (n + 1) := rfl
  have hHom (x : (normalizedChainComplex k A A).X n) :
      ((regularNormalizedComplexIso k A).hom.f n).hom x = x :=
    (LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (regularNormalizedComplexIso_hom_f k A n)) x).trans (by rfl)
  have hInv (y : (NonUnital.normalizedBComplex k A).X (n + 1)) :
      ((regularNormalizedComplexIso k A).inv.f (n + 1)).hom y = y :=
    (LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (regularNormalizedComplexIso_inv_f k A (n + 1))) y).trans (by rfl)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hPoint := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hComponent) x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hPoint
  have hB := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (NonUnital.normalizedBoundaryHomotopy_hom k A n)) x
  have hOriginal := LinearMap.congr_fun (regularNormalizedConnes_hom k A n) x
  exact hPoint.trans ((hInv _).trans
    ((congrArg ((NonUnital.normalizedBoundaryHomotopy k A).hom n (n + 1)).hom (hHom x)).trans
      (hB.trans hOriginal.symm)))

/-- The original regular normalized B on Hochschild homology. -/
def regularNormalizedConnesHomology (n : ℕ) :
    (normalizedChainComplex k A A).homology n ⟶ (normalizedChainComplex k A A).homology (n + 1) :=
  (regularNormalizedBoundaryHomotopy k A).homologyDegreeMap
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- The original B sends an cycle class to the class of its literal original B value. -/
theorem regularNormalizedConnesHomology_cycle
    (n : ℕ) (x : (normalizedChainComplex k A A).X n)
    (hx : ((normalizedChainComplex k A A).sc n).g x = 0) :
    regularNormalizedConnesHomology k A n
      (HomologicalComplex.moduleCatCycleClass (normalizedChainComplex k A A) n x hx) =
        HomologicalComplex.moduleCatCycleClass (normalizedChainComplex k A A) (n + 1)
          (regularNormalizedConnes k A n x) (by
            simpa only [regularNormalizedBoundaryHomotopy_hom] using
              (regularNormalizedBoundaryHomotopy k A).moduleCat_component_cycle
                (j := n + 1) x hx) := by
  simpa only [regularNormalizedConnesHomology, regularNormalizedBoundaryHomotopy_hom] using
    (regularNormalizedBoundaryHomotopy k A).homologyDegreeMap_moduleCatCycleClass
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) x hx

/-- The original B retains square zero on its normalized homology objects. -/
theorem regularNormalizedConnesHomology_square (n : ℕ) :
    regularNormalizedConnesHomology k A n ≫ regularNormalizedConnesHomology k A (n + 1) = 0 := by
  refine Homotopy.homologyDegreeMap_comp_eq_zero
    (regularNormalizedBoundaryHomotopy k A)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))
      (regularNormalizedBoundaryHomotopy k A) ?_
  simpa only [regularNormalizedBoundaryHomotopy_hom] using regularNormalizedConnes_square k A n

end ModuleCat.Algebra.Hochschild.Symmetric
