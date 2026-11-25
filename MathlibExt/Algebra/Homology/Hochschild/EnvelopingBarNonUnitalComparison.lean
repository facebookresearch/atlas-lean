/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Identity comparison of the two original coefficient Hochschild presentations. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarCoefficientComparison
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Basic

/-!
# Explicit and monadic coefficient Hochschild presentations

Specializing the nonunital coefficient representations
to unital bimodule actions gives the same tensor levels
and first-right, interior and last-left faces as the
monadic coefficient bar. The comparison is the identity
in every degree.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.EnvelopingCoefficient

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- The explicit engine, with exactly the two original coefficient actions. -/
def originalExplicitComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  NonUnital.complex (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom
    (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom
    (fun a b m => smul_comm a b m)

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
private theorem originalExplicitFace_tprod (n : ℕ) (i : Fin (n + 2)) (m : M) (a : Fin (n + 1) → A) :
    (NonUnital.face (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom
      (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom
      (fun a b m => smul_comm a b m) n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        faceValue k A M n i m a := by
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
  · have h := NonUnital.face_first_tprod (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom
      (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom
      (fun a b m => smul_comm a b m) n m a
    have hρ : (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom (MulOpposite.op (a 0)) m =
        MulOpposite.op (a 0) • m := rfl
    rw [faceValue, Fin.cases_zero]
    exact h.trans (congrArg (fun y : M => y ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a)) hρ)
  · have hl := NonUnital.face_last_tprod (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom
      (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom
      (fun a b m => smul_comm a b m) n m a
    have hr : faceValue k A M n (Fin.last n).succ m a =
        (a (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a) := by
      simp only [faceValue, Fin.cases_succ, Fin.lastCases_last]
    erw [hr]
    have hρ : (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom (a (Fin.last n)) m =
        a (Fin.last n) • m := rfl
    have hl' :
        (NonUnital.face (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom
          (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom
          (fun a b m => smul_comm a b m) n (Fin.last n).succ).hom
          (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom (a (Fin.last n)) m ⊗ₜ[k]
          PiTensorProduct.tprod k (hochschildDropLast a) := by
      simpa only [Fin.succ_last] using hl
    exact hl'.trans (congrArg (fun y : M => y ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a)) hρ)
  · simpa only [faceValue, Fin.cases_succ, Fin.lastCases_castSucc] using
      NonUnital.face_inner_tprod (Algebra.lsmul (A := A) k k M).toNonUnitalAlgHom
        (Algebra.lsmul (A := Aᵐᵒᵖ) k k M).toNonUnitalAlgHom
        (fun a b m => smul_comm a b m) n l m a

/-- The original explicit and canonical coefficient differentials are exactly equal as native maps. -/
theorem originalExplicitComplex_d (n : ℕ) :
    ((originalExplicitComplex k A M).d (n + 1) n).hom =
      ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  dsimp only [originalExplicitComplex]
  erw [NonUnital.complex_d,
    ModuleCat.Algebra.Hochschild.chainComplex_d, ModuleCat.Algebra.Hochschild.boundary_tprod]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  erw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  erw [LinearMap.smul_apply, originalExplicitFace_tprod]

/-- The original two Hochschild presentations agree by native identity components in every degree. -/
def originalExplicitChainIso : originalExplicitComplex k A M ≅
    ModuleCat.Algebra.Hochschild.chainComplex k A M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    erw [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    exact (originalExplicitComplex_d k A M j).symm)

/-- The explicit original coefficient engine computes the derived
balanced tensor through the original projective bar; no coefficient projectivity is needed. -/
def originalExplicitHomologyIsoDerived [Module.Projective k A] (n : ℕ) :
    (originalExplicitComplex k A M).homology n ≅
      ((AdjacentBar.coefficientTensorFunctor k A M).leftDerived n).obj
        (AdjacentBar.regularEnvelopingTarget k A) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) n).mapIso
    (originalExplicitChainIso k A M) ≪≫ AdjacentBar.coefficientHochschildHomologyIsoDerived k A M n

end ModuleCat.Algebra.Hochschild.EnvelopingCoefficient
