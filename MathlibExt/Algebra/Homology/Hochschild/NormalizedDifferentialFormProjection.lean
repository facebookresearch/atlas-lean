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
# Differential-form projection of normalized Hochschild chains

Let `k` be a commutative ring, `A` a commutative `k`-algebra, and `M` a compatible symmetric
coefficient module. The coefficient form projection sends `m ⊗ (a₀ ⊗ ⋯ ⊗ a_(n-1))` to `m ⊗
(da₀ ∧ ⋯ ∧ da_(n-1))`.

Since `d1 = 0`, this projection kills every unit degeneracy. It therefore descends to a chain
map from normalized Hochschild chains to the zero-differential coefficient-form complex. The
descended map composed with normalized projection is the full coefficient-form chain map in
every degree. The construction is integral and retains the independent coefficient universe.
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

/-- Vanishing of a differential-form projection on a unit tail factor.

If one algebra tail entry of a coefficient tensor is `1`, its image under the form projection
is zero because the corresponding universal differential is zero. -/
theorem coefficientFormProjection_unit_factor
    (n : ℕ) (m : M) (a : Fin n → A) (i : Fin n) (hi : a i = 1) :
    coefficientFormProjection k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) = 0 := by
  rw [coefficientFormProjection_tprod]
  have hD : (fun j => KaehlerDifferential.D k A (a j)) i = 0 := by
    dsimp only
    rw [hi, Derivation.map_one_eq_zero]
  rw [(exteriorPower.ιMulti A n).map_coord_zero i hD, TensorProduct.tmul_zero]

/-- The coefficient-form chain projection kills unit degeneracies.

Inserting a unit into any Hochschild tail position and then applying the coefficient
differential-form chain map gives the zero map. -/
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

/-- The normalized coefficient differential-form chain projection.

The coefficient-form chain map descends through Hochschild normalization by its vanishing on
every unit degeneracy. -/
def normalizedCoefficientDifferentialFormChainMap :
    normalizedChainComplex k A M ⟶ coefficientDifferentialFormComplex k A M := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizationDesc k A M
    (coefficientDifferentialFormChainMap k A M)
    (coefficientDifferentialFormChainMap_degeneracy k A M)

/-- The chain factorization of coefficient-form projection through normalization.

The normalized projection followed by the descended coefficient-form map equals the full
coefficient-form chain map. -/
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

/-- The degreewise factorization of coefficient-form projection through normalization.

In each degree, the factorwise normalized quotient map followed by the descended form-map
component equals the coefficient-form component on the full tensor level. -/
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
