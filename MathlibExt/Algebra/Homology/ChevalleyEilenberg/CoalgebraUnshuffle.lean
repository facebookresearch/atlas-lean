/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraComponents
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNative
public import MathlibExt.LinearAlgebra.ExteriorPower.UnshuffleCoproduct
import Lean.Elab.Tactic.Omega

/-!
# Unshuffle formulas for the Chevalley–Eilenberg coproduct

Diagonal expansion and the shuffle-coset bijection identify the homogeneous
coproduct components with the exterior unshuffle maps. This gives the finite
unshuffle formula for the chain coproduct and its coderivation equation in
every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- In every bidegree, the projected coproduct is the native general unshuffle. -/
theorem coproductComponent_eq_unshuffle (p q : ℕ) :
    coproductComponent R L (p + q) p q = exteriorPower.unshuffle R L p q := by
  apply LinearMap.ext
  intro a
  rw [coproductComponent_apply]
  exact LinearMap.congr_fun (exteriorPower.projectedCoproduct_eq_unshuffle R L p q) a

/-- Arithmetic transport of the unshuffle source degree. -/
def unshuffleOfSumEq (n p q : ℕ) (h : p + q = n) :
    (⋀[R]^n L) →ₗ[R] ((⋀[R]^p L) ⊗[R] (⋀[R]^q L)) := by
  subst n
  exact exteriorPower.unshuffle R L p q

theorem coproductComponent_eq_unshuffleOfSumEq (n p q : ℕ) (h : p + q = n) :
    coproductComponent R L n p q = unshuffleOfSumEq R L n p q h := by
  subst n
  exact coproductComponent_eq_unshuffle R L p q

/-- The all-degree unshuffle differential equation, with both empty blocks included. -/
theorem unshuffle_boundary (n p q : ℕ) (h : p + q = n) :
    (unshuffleOfSumEq R L n p q h).comp (differential R L n) =
      ((differential R L p).rTensor (⋀[R]^q L)).comp
          (unshuffleOfSumEq R L (n + 1) (p + 1) q (by omega)) +
        (-1 : R) ^ p • ((differential R L q).lTensor (⋀[R]^p L)).comp
          (unshuffleOfSumEq R L (n + 1) p (q + 1) (by omega)) := by
  rw [← coproductComponent_eq_unshuffleOfSumEq,
    ← coproductComponent_eq_unshuffleOfSumEq, ← coproductComponent_eq_unshuffleOfSumEq]
  exact coproductComponent_boundary R L n p q

/-- The native CE chain coproduct has the full finite general-unshuffle formula. -/
theorem nativeComplexComul_apply_ιMulti (n : ℕ) (w : Fin n → L) :
    ((nativeComplexComul R L).f n).hom (exteriorPower.ιMulti R n w) =
      ∑ p : Fin (n + 1),
        (ExteriorAlgebra.tensorDegreeι R L p.val (n - p.val) n
          (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))).hom
            (unshuffleOfSumEq R L n p.val (n - p.val)
              (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)) (exteriorPower.ιMulti R n w)) := by
  rw [nativeComplexComul_f]
  simp only [ExteriorAlgebra.gradedCoproduct, ExteriorAlgebra.tensorDegreeLift,
    Preadditive.comp_sum, ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.sum_apply, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe]
  have hSum :
      (ModuleCat.ofHom ((ExteriorAlgebra.coproduct R L).comp (⋀[R]^n L).subtype) ≫
        ∑ p : Fin (n + 1), ModuleCat.ofHom
          (TensorProduct.map (exteriorPower.projection R L p.val)
            (exteriorPower.projection R L (n - p.val))) ≫
          ExteriorAlgebra.tensorDegreeι R L p.val (n - p.val) n (by omega)).hom
        (exteriorPower.ιMulti R n w) =
      ∑ p : Fin (n + 1),
        (ModuleCat.ofHom ((ExteriorAlgebra.coproduct R L).comp (⋀[R]^n L).subtype) ≫
          ModuleCat.ofHom (TensorProduct.map (exteriorPower.projection R L p.val)
            (exteriorPower.projection R L (n - p.val))) ≫
          ExteriorAlgebra.tensorDegreeι R L p.val (n - p.val) n (by omega)).hom
          (exteriorPower.ιMulti R n w) := by
    rw [Preadditive.comp_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  exact hSum.trans (by
    apply Finset.sum_congr rfl
    intro p _
    rw [← coproductComponent_eq_unshuffleOfSumEq, coproductComponent_apply]
    change (ExteriorAlgebra.tensorDegreeι R L p.val (n - p.val) n (by omega)).hom
      (TensorProduct.map (exteriorPower.projection R L p.val)
        (exteriorPower.projection R L (n - p.val))
        (ExteriorAlgebra.coproduct R L (exteriorPower.ιMulti R n w : ExteriorAlgebra R L))) = _
    rfl)

end ChevalleyEilenberg
