/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricRegularNormalized
public import MathlibExt.Algebra.Homology.HomologicalComplex.ConcreteHomotopyClass

/-!
# Regular normalized Connes maps on homology

For a commutative k-algebra A, the normalized Connes operator Bₙ : C̄ₙ(A,A) → C̄ₙ₊₁(A,A)
satisfies bB+Bb=0 and B²=0. Transporting the regular normalized mixed-complex operator to the
symmetric coefficient complex packages B as a homotopy from the zero chain map to itself.

This degree-one homotopy induces maps B : Hₙ(C̄(A,A)) → Hₙ₊₁(C̄(A,A)). On a cycle x the map is
[x] ↦ [Bₙx], and consecutive induced maps compose to zero. The construction is over an arbitrary
commutative ground ring.

For Connes' operator and the normalized mixed complex, see J.-L. Loday, Cyclic Homology, second
edition, §2.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients and b its Hochschild differential. The
degree-one operator B, transported through regularNormalizedComplexIso, defines a homotopy from
the zero chain endomorphism of C̄(A,A) to itself. Its homotopy equation is bB+Bb=0. -/
def regularNormalizedBoundaryHomotopy :
    Homotopy (0 : normalizedChainComplex k A A ⟶ normalizedChainComplex k A A) 0 := by
  let e := regularNormalizedComplexIso k A
  let H := ((NonUnital.normalizedBoundaryHomotopy k A).compLeft e.hom).compRight e.inv
  refine { hom := H.hom, zero := H.zero, comm := ?_ }
  intro n
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply,
    Limits.comp_zero, Limits.zero_comp] using H.comm n

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients and b its Hochschild differential. For n : ℕ,
the component of regularNormalizedBoundaryHomotopy from degree n to n+1 equals
regularNormalizedConnes k A n : C̄ₙ(A,A) → C̄ₙ₊₁(A,A). -/
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

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients and b its Hochschild differential. The
zero-to-zero homotopy determined by B induces regularNormalizedConnesHomology : Hₙ(C̄(A,A)) →
Hₙ₊₁(C̄(A,A)) for every n : ℕ. -/
def regularNormalizedConnesHomology (n : ℕ) :
    (normalizedChainComplex k A A).homology n ⟶ (normalizedChainComplex k A A).homology (n + 1) :=
  (regularNormalizedBoundaryHomotopy k A).homologyDegreeMap
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients and b its Hochschild differential. If x ∈
C̄ₙ(A,A) satisfies bx=0, then regularNormalizedConnesHomology k A n sends its homology class [x]
to [regularNormalizedConnes k A n x] in degree n+1. The relation bB+Bb=0 ensures the latter is a
cycle. -/
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

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients and b its Hochschild differential. For every
n : ℕ, regularNormalizedConnesHomology k A n followed by regularNormalizedConnesHomology k A
(n+1) is zero, by the square-zero identity for B on chains. -/
theorem regularNormalizedConnesHomology_square (n : ℕ) :
    regularNormalizedConnesHomology k A n ≫ regularNormalizedConnesHomology k A (n + 1) = 0 := by
  refine Homotopy.homologyDegreeMap_comp_eq_zero
    (regularNormalizedBoundaryHomotopy k A)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))
      (regularNormalizedBoundaryHomotopy k A) ?_
  simpa only [regularNormalizedBoundaryHomotopy_hom] using regularNormalizedConnes_square k A n

end ModuleCat.Algebra.Hochschild.Symmetric
