/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel

/-!
# Ordinary use of the finite-idempotent projective model

The complete public characteristics retain exactness, the actual range action,
all free matrix maps, both block factors, and the regular successor.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace FGProjectiveCat.IdempotentModelTests

variable (A : Type u) [Ring A]

/-- The ordinary interface preserves arbitrary ranges and full free-block maps. -/
theorem canonicalModelClient (n m : ℕ) (b : Matrix (Fin n) (Fin m) A)
    (g : Matrix.GeneralLinearGroup (Fin n) A) (h : Matrix.GeneralLinearGroup (Fin m) A)
    (P Q : FGProjectiveCat.IdempotentModel A) (f : P ⟶ Q)
    (x : FGProjectiveCat.IdempotentModel.range A P) :
    let C := FGProjectiveCat.FiniteRowRanks A
    let E := FGProjectiveCat.IdempotentModel.equivalence A
    let F := fun k : ℕ => (Idempotents.toKaroubi C).obj k
    let H := fun k => FGProjectiveCat.IdempotentModel.freeIso A k
    let B := FGProjectiveCat.IdempotentModel.freeBiprodIso A n m
    let S := FGProjectiveCat.IdempotentModel.regularSuccessorIso A n
    let a := fun {U V : FGProjectiveCat.IdempotentModel A} (z : U ⟶ V) =>
      FGProjectiveCat.IdempotentModel.rowHomEquiv A U.X V.X z.f
    let r := fun U : FGProjectiveCat.IdempotentModel A =>
      eqToIso (FGProjectiveCat.IdempotentModel.equivalence_obj A U)
    let γ := fun k (z : (Matrix.GeneralLinearGroup (Fin k) A)ᵐᵒᵖ) =>
      FGProjectiveCat.IdempotentModel.freeAut A k z
    let d := Matrix.GeneralLinearGroup.reindexMulEquiv
      (finSumFinEquiv (m := n) (n := m))
      (Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal g h)
    E.functor.IsExact ∧ E.inverse.IsExact ∧
      (∀ u v : P ⟶ Q, a u = a v → u = v) ∧
      (((r P).inv ≫ E.functor.map f ≫ (r Q).hom).hom.hom x).val =
        (a f).toLinearMapRight' x.val ∧
      (E.functor.map ((Idempotents.toKaroubi C).map
          ((FGProjectiveCat.IdempotentModel.rowHomEquiv A n m).symm b)) ≫ (H m).hom =
        (H n).hom ≫ FGProjectiveCat.ofHom b.toLinearMapRight') ∧
      (∃ h : IsZero (F 0), FGProjectiveCat.IdempotentModel.freeZeroIso A = h.isoZero) ∧
      (∀ y : FGProjectiveCat.IdempotentModel.range A (F 1),
        ((r (F 1)).inv ≫ (FGProjectiveCat.IdempotentModel.regularIso A).hom).hom.hom y =
          y.val (0 : Fin 1)) ∧
      (E.functor.mapIso B ≪≫ E.functor.mapBiprod (F n) (F m) ≪≫ biprod.mapIso (H n) (H m) =
        H (n + m) ≪≫ FGProjectiveCat.standardFreeAddIso A n m) ∧
      (γ (n + m) (MulOpposite.op d) = (B.symm.conjAut
        (Aut.of (biprod.mapIso (γ n (MulOpposite.op g))
          (γ m (MulOpposite.op h))))).asIso) ∧
      (S.conjAut (Aut.of (E.functor.mapIso
          (γ (n + 1) (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization A g))))) =
        Aut.of (biprod.mapIso
          (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n (MulOpposite.op g)).asIso
          (Iso.refl (FGProjectiveCat.regular A)))) := by
  dsimp only
  have e := FGProjectiveCat.IdempotentModel.equivalence_characteristic A
  have k := FGProjectiveCat.IdempotentModel.free_characteristic A
  have z := FGProjectiveCat.IdempotentModel.free_block_characteristic A
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v hu
    exact (e.2.2.2.2.2.2.2.2.1 P Q u v).1 hu
  · exact e.2.2.2.2.2.2.2.2.2.2.1 P Q f x
  · exact k.2.2.2.1 n m b
  · exact ⟨k.2.2.2.2.1,
      FGProjectiveCat.IdempotentModel.freeZeroIso_characteristic A k.2.2.2.2.1⟩
  · exact k.2.2.2.2.2.1
  · exact z.2.2.1 n m
  · exact z.2.2.2.2.1 n m g h
  · exact z.2.2.2.2.2.2.2.2.2 n g

end FGProjectiveCat.IdempotentModelTests
