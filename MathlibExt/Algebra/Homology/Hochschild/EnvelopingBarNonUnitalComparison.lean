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
# Explicit coefficient boundaries and the enveloping bar

Let `k` be a commutative ring, `A` a unital `k`-algebra, and `M` a bimodule with commuting
left and right actions compatible with `k`. Specializing the explicit nonunital coefficient
construction to these unital actions gives degree `n` equal to `M ⊗[k] A^⊗n`.

Its faces agree with the coefficient bar faces: the first face uses the right coefficient
action, interior faces multiply adjacent algebra factors, and the last face uses the left
coefficient action. Thus its signed boundary equals the coefficient Hochschild boundary, and
identity degree maps give a chain isomorphism. If `Module.Projective k A`, its homology
computes the left-derived coefficient balanced-tensor functor at the regular enveloping module
`A`. The coefficient carrier universe remains independent.
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

/-- The explicit coefficient complex specialized to unital bimodule actions.

Use the left and right multiplication representations of a bimodule `M` in the explicit
nonunital construction. The resulting chain complex has degree `n` equal to `M ⊗[k] A^⊗n`. -/
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

/-- Equality of explicit and coefficient Hochschild differentials.

In every successor degree, the explicit boundary agrees with the coefficient Hochschild
boundary on the common tensor carrier, retaining the first-right and last-left coefficient
actions. -/
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

/-- The identity comparison of two coefficient Hochschild complexes.

Identity maps on the degreewise coefficient tensor modules give a chain isomorphism from the
explicit unital specialization to the coefficient Hochschild chain complex. -/
def originalExplicitChainIso : originalExplicitComplex k A M ≅
    ModuleCat.Algebra.Hochschild.chainComplex k A M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    erw [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    exact (originalExplicitComplex_d k A M j).symm)

/-- The derived balanced-tensor comparison for explicit coefficient chains.

If `Module.Projective k A`, degree-`n` homology of the explicit coefficient complex is
isomorphic to the `n`th left-derived coefficient balanced-tensor value on the regular
enveloping module `A`. The coefficient module has its given bimodule actions. -/
def originalExplicitHomologyIsoDerived [Module.Projective k A] (n : ℕ) :
    (originalExplicitComplex k A M).homology n ≅
      ((AdjacentBar.coefficientTensorFunctor k A M).leftDerived n).obj
        (AdjacentBar.regularEnvelopingTarget k A) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) n).mapIso
    (originalExplicitChainIso k A M) ≪≫ AdjacentBar.coefficientHochschildHomologyIsoDerived k A M n

end ModuleCat.Algebra.Hochschild.EnvelopingCoefficient
