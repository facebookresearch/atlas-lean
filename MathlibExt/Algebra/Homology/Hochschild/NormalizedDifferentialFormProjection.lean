/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormNaturality
public import MathlibExt.Algebra.Homology.Hochschild.Normalized

/-!
# normalized descent of the differential-form projection

The universal differential of the unit is zero. Thus the raw
coefficient projection kills every original unit degeneracy, and the native
Hochschild normalization universal property constructs its unique normalized
chain map. This uses the original ground-unit quotient and introduces no
algebra structure on that quotient.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- A original unit factor is killed by the differential-form projection. -/
theorem coefficientFormProjection_unit_factor
    (n : ℕ) (m : M) (a : Fin n → A) (i : Fin n) (hi : a i = 1) :
    coefficientFormProjection k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) = 0 := by
  rw [coefficientFormProjection_tprod]
  have hD : (fun j => KaehlerDifferential.D k A (a j)) i = 0 := by
    dsimp only
    rw [hi, Derivation.map_one_eq_zero]
  rw [(exteriorPower.ιMulti A n).map_coord_zero i hD, TensorProduct.tmul_zero]

/-- Every original unit degeneracy vanishes after the constructed raw chain projection. -/
theorem coefficientDifferentialFormChainMap_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    ModuleCat.Algebra.Hochschild.degeneracy k A M n i ≫
      (coefficientDifferentialFormChainMap k A M).f (n + 1) = 0 := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  let g : (ModuleCat.Algebra.Hochschild.chainComplex k A M).X n ⟶
      (ModuleCat.Algebra.Hochschild.chainComplex k A M).X (n + 1) :=
    ModuleCat.Algebra.Hochschild.degeneracy k A M n i
  let p := (coefficientDifferentialFormChainMap k A M).f (n + 1)
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  let z : (ModuleCat.Algebra.Hochschild.chainComplex k A M).X n :=
    m ⊗ₜ[k] PiTensorProduct.tprod k a
  let z' : (ModuleCat.Algebra.Hochschild.chainComplex k A M).X (n + 1) :=
    m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildInsertOne i a)
  have hc : (g ≫ p).hom z = p.hom (g.hom z) := ModuleCat.comp_apply g p z
  have hd : g.hom z = z' := ModuleCat.Algebra.Hochschild.degeneracy_tprod k A M n i m a
  have hp : p.hom z' =
      (ULift.up (coefficientFormProjection k A M (n + 1) z') :
        (coefficientDifferentialFormComplex k A M).X (n + 1)) := rfl
  have hz : coefficientFormProjection k A M (n + 1) z' = 0 :=
    coefficientFormProjection_unit_factor k A M (n + 1) m
      (hochschildInsertOne i a) i (by simp only [hochschildInsertOne, Fin.insertNth_apply_same])
  have hzero : (ULift.up (0 : M ⊗[A] (⋀[A]^(n + 1) (KaehlerDifferential k A))) :
      (coefficientDifferentialFormComplex k A M).X (n + 1)) = 0 := rfl
  exact hc.trans ((congrArg p.hom hd).trans
    (hp.trans ((congrArg (fun b : M ⊗[A] (⋀[A]^(n + 1) (KaehlerDifferential k A)) =>
      (ULift.up b : (coefficientDifferentialFormComplex k A M).X (n + 1))) hz).trans hzero)))

/-- Native normalized descent of the original raw projection to coefficient forms. -/
def normalizedCoefficientDifferentialFormChainMap :
    normalizedChainComplex k A M ⟶ coefficientDifferentialFormComplex k A M := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizationDesc k A M
    (coefficientDifferentialFormChainMap k A M)
    (coefficientDifferentialFormChainMap_degeneracy k A M)

/-- The normalized projection retains the original raw chain-map square. -/
@[reassoc]
theorem normalizationProjection_differentialForms :
    normalizationProjection k A M ≫ normalizedCoefficientDifferentialFormChainMap k A M =
      coefficientDifferentialFormChainMap k A M := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizationProjection_desc k A M
    (coefficientDifferentialFormChainMap k A M)
    (coefficientDifferentialFormChainMap_degeneracy k A M)

/-- Every descended degree has the original factorwise normalization representative law. -/
theorem normalizationLevelMap_differentialForms (n : ℕ) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M n ≫
      (normalizedCoefficientDifferentialFormChainMap k A M).f n =
        (coefficientDifferentialFormChainMap k A M).f n := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizationLevelMap_desc_f k A M
    (coefficientDifferentialFormChainMap k A M)
    (coefficientDifferentialFormChainMap_degeneracy k A M) n

end ModuleCat.Algebra.Hochschild.Symmetric
