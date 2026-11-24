/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficients
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedQuotient

/-!
# Symmetric Hochschild normalization homotopy equivalence

Full Hochschild normalization has its projection as forward map
and an exact chain section as inverse. The section-projection
composite is homotopic to the identity through the Dold–Kan
quotient homotopy. Proper-shuffle descent uses the rational
Eulerian relation kernels.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The raw/bar and normalized tensor coordinates transport the normalization homotopy. -/
def normalizationHomotopyEquiv :
    HomotopyEquiv (chainComplex k A M) (normalizedChainComplex k A M) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  let c := chainComplexIso k A M
  let n := AlgebraicTopology.NormalizedQuotient.projectionHomotopyEquiv (coefficientBar k A M)
  let e := ModuleCat.Algebra.Hochschild.normalizationIso k A M
  let h := (HomotopyEquiv.ofIso c).trans (n.trans (HomotopyEquiv.ofIso e))
  have hforward : h.hom = normalizationProjection k A M := by
    change c.hom ≫ (n.hom ≫ e.hom) = (c.hom ≫ n.hom) ≫ e.hom
    exact (Category.assoc _ _ _).symm
  exact h.copy (Homotopy.ofEq hforward)

/-- The transported equivalence retains the original factorwise normalization map. -/
theorem normalizationHomotopyEquiv_hom :
    (normalizationHomotopyEquiv k A M).hom = normalizationProjection k A M :=
  rfl

/-- Its inverse has the original normalized tensor, native Moore and raw-bar coordinates. -/
theorem normalizationHomotopyEquiv_inv :
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  (normalizationHomotopyEquiv k A M).inv =
    ((ModuleCat.Algebra.Hochschild.normalizationIso k A M).inv ≫
      ((AlgebraicTopology.NormalizedQuotient.mooreIso (coefficientBar k A M)).hom ≫
        AlgebraicTopology.inclusionOfMooreComplexMap (coefficientBar k A M))) ≫
      (chainComplexIso k A M).inv :=
  rfl

/-- The transported inverse is an exact right inverse to normalization. -/
@[reassoc]
theorem normalizationHomotopyEquiv_inv_hom :
    (normalizationHomotopyEquiv k A M).inv ≫ normalizationProjection k A M =
      𝟙 (normalizedChainComplex k A M) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  let X := coefficientBar k A M
  let c : chainComplex k A M ≅
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj X :=
    chainComplexIso k A M
  let e : AlgebraicTopology.NormalizedQuotient.obj X ≅ normalizedChainComplex k A M :=
    ModuleCat.Algebra.Hochschild.normalizationIso k A M
  let p := AlgebraicTopology.NormalizedQuotient.projection X
  let r := (AlgebraicTopology.NormalizedQuotient.mooreIso X).hom ≫
    AlgebraicTopology.inclusionOfMooreComplexMap X
  have hr : r ≫ p = 𝟙 _ := by
    change ((AlgebraicTopology.NormalizedQuotient.mooreIso X).hom ≫
        AlgebraicTopology.inclusionOfMooreComplexMap X) ≫ p = 𝟙 _
    rw [Category.assoc, ← AlgebraicTopology.NormalizedQuotient.mooreIso_inv X]
    exact (AlgebraicTopology.NormalizedQuotient.mooreIso X).hom_inv_id
  rw [normalizationHomotopyEquiv_inv]
  change ((e.inv ≫ r) ≫ c.inv) ≫ ((c.hom ≫ p) ≫ e.hom) = 𝟙 _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc r p e.hom, hr, Category.id_comp]
  exact e.inv_hom_id

/-- The contraction homotopy is retained in the original coefficient complex. -/
def normalizationHomotopy :
    Homotopy (normalizationProjection k A M ≫ (normalizationHomotopyEquiv k A M).inv)
      (𝟙 (chainComplex k A M)) :=
  (normalizationHomotopyEquiv k A M).homotopyHomInvId

end ModuleCat.Algebra.Hochschild.Symmetric
