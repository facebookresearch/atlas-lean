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
# Homotopy equivalence for symmetric Hochschild normalization

Let k be a commutative ring, A a commutative k-algebra and M a compatible symmetric coefficient
module. The factorwise quotient projection Cₙ(A,M) → C̄ₙ(A,M), applying A → A/(k·1) to each
tail, is the forward map of a chain homotopy equivalence.

The inverse section is obtained by identifying the normalized bar quotient with its Moore
complex, including that Moore complex into the alternating-face bar complex, and returning to
raw tensor coordinates. The section followed by normalization is exactly the identity of the
normalized complex. Normalization followed by the section is homotopic to the identity of the
raw complex through the quotient normalization homotopy. These statements require no rationality
or coefficient-flatness hypothesis.

For Hochschild normalization, see J.-L. Loday, Cyclic Homology, second edition, §1.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let C and C̄ be the raw and normalized Hochschild chain complexes over
k, indexed by ℕ. Transporting the simplicial bar normalization homotopy equivalence through the
raw and normalized tensor coordinate isomorphisms gives normalizationHomotopyEquiv :
HomotopyEquiv C C̄. Its forward map is the factorwise quotient projection and its inverse is the
Moore-complex section. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let C and C̄ be the raw and normalized Hochschild chain complexes over
k, indexed by ℕ. The forward map of normalizationHomotopyEquiv k A M equals
normalizationProjection k A M, which applies A → A/(k·1) to each algebra tail and leaves the
coefficient unchanged. -/
theorem normalizationHomotopyEquiv_hom :
    (normalizationHomotopyEquiv k A M).hom = normalizationProjection k A M :=
  rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let C and C̄ be the raw and normalized Hochschild chain complexes over
k, indexed by ℕ. The inverse map first takes normalized tensor coordinates to the normalized
quotient of the coefficient bar, then uses its isomorphism to the Moore complex, includes the
Moore complex into the alternating-face bar complex, and returns to raw tensor coordinates
through chainComplexIso.inv. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let C and C̄ be the raw and normalized Hochschild chain complexes over
k, indexed by ℕ. If s = (normalizationHomotopyEquiv k A M).inv and π = normalizationProjection k
A M, then s ≫ π = 𝟙 C̄ as chain maps. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let C and C̄ be the raw and normalized Hochschild chain complexes over
k, indexed by ℕ. There is a chain homotopy from normalizationProjection k A M followed by
(normalizationHomotopyEquiv k A M).inv to the identity of chainComplex k A M. This is the
quotient normalization homotopy transported to the tensor complex. -/
def normalizationHomotopy :
    Homotopy (normalizationProjection k A M ≫ (normalizationHomotopyEquiv k A M).inv)
      (𝟙 (chainComplex k A M)) :=
  (normalizationHomotopyEquiv k A M).homotopyHomInvId

end ModuleCat.Algebra.Hochschild.Symmetric
