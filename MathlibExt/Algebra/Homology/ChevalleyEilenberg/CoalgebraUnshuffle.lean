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
# Exterior unshuffles in the Chevalley–Eilenberg chain coproduct

Let R be commutative and L an R-Lie algebra. In source degree p+q,
the projected coproduct is the exterior unshuffle
U_{p,q}:Λ_R^{p+q}L→Λ_R^pL⊗_RΛ_R^qL.
For an ordered wedge, it sums over p-element subsets I and their
complements J, with both blocks in increasing order. The coefficient
is the sign of the permutation whose ordered blocks are (I,J).

Under p+q=n, write U_{n;p,q} for the same map with source Λ_R^nL.
Then
U_{n;p,q}d_n=(d_p⊗id)U_{n+1;p+1,q}
+(−1)^p(id⊗d_q)U_{n+1;p,q+1}.
The chain coproduct is ∑_{p+q=n} ι_{p,q}U_{p,q}, including both
empty-block terms. All coefficients are integral.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
Write π_p:E→Λ_R^pL for the homogeneous projection and
d_p:Λ_R^{p+1}L→Λ_R^pL for the restricted boundary.
In degree n=p+q, the projected primitive coproduct is the
exterior unshuffle: c_{p+q;p,q}=U_{p,q}. Its two blocks retain
their internal order and have the unshuffle permutation sign. -/
theorem coproductComponent_eq_unshuffle (p q : ℕ) :
    coproductComponent R L (p + q) p q = exteriorPower.unshuffle R L p q := by
  apply LinearMap.ext
  intro a
  rw [coproductComponent_apply]
  exact LinearMap.congr_fun (exteriorPower.projectedCoproduct_eq_unshuffle R L p q) a

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
Write π_p:E→Λ_R^pL for the homogeneous projection and
d_p:Λ_R^{p+1}L→Λ_R^pL for the restricted boundary.
For a specified equality p+q=n, the exterior unshuffle gives
U_{n;p,q}:Λ_R^nL→Λ_R^pL⊗Λ_R^qL with that source degree. -/
def unshuffleOfSumEq (n p q : ℕ) (h : p + q = n) :
    (⋀[R]^n L) →ₗ[R] ((⋀[R]^p L) ⊗[R] (⋀[R]^q L)) := by
  subst n
  exact exteriorPower.unshuffle R L p q

theorem coproductComponent_eq_unshuffleOfSumEq (n p q : ℕ) (h : p + q = n) :
    coproductComponent R L n p q = unshuffleOfSumEq R L n p q h := by
  subst n
  exact coproductComponent_eq_unshuffle R L p q

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
Write π_p:E→Λ_R^pL for the homogeneous projection and
d_p:Λ_R^{p+1}L→Λ_R^pL for the restricted boundary.
For p+q=n, the unshuffle differential square is
U_{n;p,q}d_n=(d_p⊗id)U_{n+1;p+1,q}
+(−1)^p(id⊗d_q)U_{n+1;p,q+1}.
This includes p=0 and q=0. -/
theorem unshuffle_boundary (n p q : ℕ) (h : p + q = n) :
    (unshuffleOfSumEq R L n p q h).comp (differential R L n) =
      ((differential R L p).rTensor (⋀[R]^q L)).comp
          (unshuffleOfSumEq R L (n + 1) (p + 1) q (by omega)) +
        (-1 : R) ^ p • ((differential R L q).lTensor (⋀[R]^p L)).comp
          (unshuffleOfSumEq R L (n + 1) p (q + 1) (by omega)) := by
  rw [← coproductComponent_eq_unshuffleOfSumEq,
    ← coproductComponent_eq_unshuffleOfSumEq, ← coproductComponent_eq_unshuffleOfSumEq]
  exact coproductComponent_boundary R L n p q

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
Write π_p:E→Λ_R^pL for the homogeneous projection and
d_p:Λ_R^{p+1}L→Λ_R^pL for the restricted boundary.
On a decomposable n-fold wedge, the chain coproduct is
∑_{p=0}^{n} ι_{p,n−p}U_{n;p,n−p}(w), where each ι
includes the corresponding tensor summand in total degree n. -/
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
