/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarCoefficientComparison
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps

/-!
# symmetric coefficients and the enveloping bar tensor

Only the canonical right action from the original A-module is added.
The neutral comparison retains the original coefficient head, original
ground tensor tails and the original Hochschild differential.
Coefficient naturality uses the all-ground-ring A-linear maps;
the comparison commutes with the original A-scalar maps as well.

No rationality, flatness, free coefficient, Small or desired comparison law
is an input. The literal first-positive/full coefficient-ideal relations
and higher Harrison/HKR statements remain separate from this raw comparison.
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

/-- The coefficient tensor of the original bar with the original symmetric right action. -/
def symmetricEnvelopingTensorComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact AdjacentBar.coefficientTensorComplex k A M

/-- The neutral bar comparison specializes to the original symmetric Hochschild complex. -/
def symmetricEnvelopingTensorChainIso : symmetricEnvelopingTensorComplex k A M ≅ chainComplex k A M := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact AdjacentBar.coefficientTensorChainIso k A M

/-- Both original outer scalars act on the original coefficient, in the original middle-word coordinates. -/
theorem symmetricEnvelopingTensorChainIso_mk_tprod (n : ℕ) (m : M) (a0 : A) (a : Fin (n + 1) → A) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (AdjacentBar.envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (AdjacentBar.EnvelopingAlgebra k A))
    (show M ⊗[k] TensorPower k n A from ((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom
      (TensorProduct.Balanced.mk k (AdjacentBar.EnvelopingAlgebra k A) M
        (AdjacentBar.envelopingBarDegree k A n).carrier m (a0 ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ((a0 * a (Fin.last n)) • m) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.init a) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (AdjacentBar.envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (AdjacentBar.EnvelopingAlgebra k A))
  change AdjacentBar.coefficientTensorLevelEquiv k A M n
    (TensorProduct.Balanced.mk k (AdjacentBar.EnvelopingAlgebra k A) M
      (AdjacentBar.envelopingBarDegree k A n).carrier m (a0 ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  simpa only [opModule_smul, MulOpposite.unop_op, smul_smul] using
    AdjacentBar.coefficientTensorLevelEquiv_mk_tprod k A M n m a0 a

section CoefficientNaturality

variable {N : Type w} [AddCommGroup N] [Module k N] [Module A N]
  [SMulCommClass k A N] [IsScalarTower k A N]

/-- The balanced tensor coefficient map is the original A-linear coefficient map with its right action. -/
def symmetricEnvelopingTensorComplexMap (f : M →ₗ[A] N) :
    symmetricEnvelopingTensorComplex k A M ⟶ symmetricEnvelopingTensorComplex k A N := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := opModule A N
  letI := actionsComm A N
  letI := kOpComm k A N
  letI := kOpTower k A N
  exact AdjacentBar.coefficientTensorComplexMap k A M (f.restrictScalars k)
    (fun a m => f.map_smul a m)
    (fun b m => by
      change f (b.unop • m) = b.unop • f m
      exact f.map_smul b.unop m)

/-- The original symmetric coefficient chain map, delegating the neutral native tensor map. -/
def symmetricOriginalCoefficientChainMap (f : M →ₗ[A] N) : chainComplex k A M ⟶ chainComplex k A N := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := opModule A N
  letI := actionsComm A N
  letI := kOpComm k A N
  letI := kOpTower k A N
  exact AdjacentBar.originalCoefficientChainMap k A M (f.restrictScalars k)
    (fun a m => f.map_smul a m)
    (fun b m => by
      change f (b.unop • m) = b.unop • f m
      exact f.map_smul b.unop m)

/-- The original A-linear coefficient component is retained exactly after ground restriction. -/
theorem symmetricOriginalCoefficientChainMap_f (f : M →ₗ[A] N) (n : ℕ) :
    ((symmetricOriginalCoefficientChainMap k A M f).f n).hom =
      (algebraCoefficientLevelMap k A f n).restrictScalars k := by
  rw [algebraCoefficientLevelMap_restrictScalars]
  rfl

/-- The forward symmetric comparison is natural in original A-linear coefficient maps. -/
@[reassoc]
theorem symmetricEnvelopingTensorChainIso_hom_naturality (f : M →ₗ[A] N) :
    symmetricEnvelopingTensorComplexMap k A M f ≫ (symmetricEnvelopingTensorChainIso k A N).hom =
      (symmetricEnvelopingTensorChainIso k A M).hom ≫ symmetricOriginalCoefficientChainMap k A M f := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := opModule A N
  letI := actionsComm A N
  letI := kOpComm k A N
  letI := kOpTower k A N
  exact AdjacentBar.coefficientTensorChainIso_hom_naturality k A M (f.restrictScalars k)
    (fun a m => f.map_smul a m)
    (fun b m => by
      change f (b.unop • m) = b.unop • f m
      exact f.map_smul b.unop m)

/-- The inverse symmetric comparison is natural too. -/
@[reassoc]
theorem symmetricEnvelopingTensorChainIso_inv_naturality (f : M →ₗ[A] N) :
    (symmetricEnvelopingTensorChainIso k A M).inv ≫ symmetricEnvelopingTensorComplexMap k A M f =
      symmetricOriginalCoefficientChainMap k A M f ≫ (symmetricEnvelopingTensorChainIso k A N).inv := by
  apply (cancel_mono (symmetricEnvelopingTensorChainIso k A N).hom).mp
  rw [Category.assoc, symmetricEnvelopingTensorChainIso_hom_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CoefficientNaturality

/-- The original A-scalar coefficient map on the tensor-of-bar complex. -/
def symmetricEnvelopingTensorScalarMap (a : A) :
    symmetricEnvelopingTensorComplex k A M ⟶ symmetricEnvelopingTensorComplex k A M :=
  symmetricEnvelopingTensorComplexMap k A M (Algebra.lsmul A A M a)

/-- The comparison preserves the original A-action, expressed by its
original scalar coefficient maps; no transported coefficient action is chosen. -/
theorem symmetricEnvelopingTensorChainIso_scalar (a : A) (n : ℕ)
    (x : (symmetricEnvelopingTensorComplex k A M).X n) :
    let y : M ⊗[k] TensorPower k n A :=
      ((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom x
    (show M ⊗[k] TensorPower k n A from
      ((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom
        (((symmetricEnvelopingTensorScalarMap k A M a).f n).hom x)) = a • y := by
  let y : M ⊗[k] TensorPower k n A :=
    ((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom x
  have h := congrArg (fun f => f.f n)
    (symmetricEnvelopingTensorChainIso_hom_naturality k A M (Algebra.lsmul A A M a))
  have hx := ConcreteCategory.congr_hom h x
  change ((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom
      (((symmetricEnvelopingTensorScalarMap k A M a).f n).hom x) =
    ((symmetricOriginalCoefficientChainMap k A M (Algebra.lsmul A A M a)).f n).hom
      (((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom x) at hx
  let s : M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n A :=
    ((symmetricOriginalCoefficientChainMap k A M (Algebra.lsmul A A M a)).f n).hom
  have hs0 : s = (algebraCoefficientLevelMap k A (Algebra.lsmul A A M a) n).restrictScalars k :=
    symmetricOriginalCoefficientChainMap_f k A M (Algebra.lsmul A A M a) n
  have hs (z : M ⊗[k] TensorPower k n A) :
      (algebraCoefficientLevelMap k A (Algebra.lsmul A A M a) n).restrictScalars k z = a • z := by
    change TensorProduct.map (Algebra.lsmul k k M a) LinearMap.id z = a • z
    exact (TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor a z).symm
  have hxy : (show M ⊗[k] TensorPower k n A from
      ((symmetricEnvelopingTensorChainIso k A M).hom.f n).hom
        (((symmetricEnvelopingTensorScalarMap k A M a).f n).hom x)) = s y := hx
  exact hxy.trans ((congrArg (fun f => f y) hs0).trans (hs y))

end ModuleCat.Algebra.Hochschild.Symmetric
