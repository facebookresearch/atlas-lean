/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientHomogeneous
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientNaturality

/-!
# Exterior-first Chevalley–Eilenberg chains with coefficients

Let R be commutative, L an R-Lie algebra and M a compatible left Lie
module. The chain term is Λ_R^nL⊗M, and its differential is the
homogeneous restriction of the ambient coefficient boundary. It is
the bracket term tensored with M plus signed coefficient deletion,
with action sign (−1)^{i+1}. The first boundary gives −[x,m].

Linear differential naturality holds for coefficient homomorphisms
with independent carrier universes. For literal categorical chain maps,
the coefficient modules occupy one universe w, and the chain category
has height max{u,v,w}. The component map is id_{Λ^nL}⊗f and
preserves identity and composition.

Changing to right coefficients uses m·x=−[x,m] and swaps the tensor
factors. No projectivity or finiteness assumption on the Lie module
is part of the chain construction.

References: C. A. Weibel, An Introduction to Homological Algebra,
Definition 7.7.1 and Corollary 7.7.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w w'

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- Let R be commutative, L an R-Lie algebra and M an R-module.
The degree-n exterior-first coefficient object is Λ_R^nL⊗M
in ModuleCat over R at height max{u,v,w}. A Lie action on M
is not needed to form this tensor object. -/
abbrev coefficientChainObject (n : ℕ) : ModuleCat.{max u v w} R :=
  ModuleCat.of R ((⋀[R]^n L) ⊗[R] M)

variable [LieRingModule L M] [LieModule R L M]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
The homogeneous coefficient boundaries define the nonnegative
R-module chain complex with degree-n term Λ_R^nL⊗M. -/
def coefficientComplex : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  ChainComplex.of (coefficientChainObject R L M)
    (fun n => ModuleCat.ofHom (coefficientDifferential R L M n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, coefficientDifferential_comp_differential,
        ModuleCat.ofHom_zero])

@[simp]
theorem coefficientComplex_X (n : ℕ) :
    (coefficientComplex R L M).X n = coefficientChainObject R L M n :=
  rfl

@[simp]
theorem coefficientComplex_d_succ (n : ℕ) :
    (coefficientComplex R L M).d (n + 1) n =
      ModuleCat.ofHom (coefficientDifferential R L M n) := by
  simp only [coefficientComplex, ChainComplex.of_d]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Every differential between degrees i,j with i≠j+1 is zero;
only consecutive descending degrees carry the coefficient boundary. -/
theorem coefficientComplex_d_eq_zero (i j : ℕ) (h : i ≠ j + 1) :
    (coefficientComplex R L M).d i j = 0 :=
  ChainComplex.of_d_ne (coefficientChainObject R L M)
    (fun n => ModuleCat.ofHom (coefficientDifferential R L M n)) h

section Naturality

variable {N : Type w'} [AddCommGroup N] [Module R N]
  [LieRingModule L N] [LieModule R L N]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For an R-Lie module homomorphism f:M→N, with N in an
independent carrier universe,
(id_{Λ^nL}⊗f)d_n^M=d_n^N(id_{Λ^{n+1}L}⊗f). -/
theorem coefficientDifferential_naturality (f : M →ₗ⁅R,L⁆ N) (n : ℕ) :
    (f.toLinearMap.lTensor (⋀[R]^n L)).comp (coefficientDifferential R L M n) =
      (coefficientDifferential R L N n).comp (f.toLinearMap.lTensor (⋀[R]^(n + 1) L)) := by
  have hinclusion (k : ℕ) (p : (⋀[R]^k L) ⊗[R] M) :
      ((⋀[R]^k L).subtype.rTensor N) ((f.toLinearMap.lTensor (⋀[R]^k L)) p) =
        (f.toLinearMap.lTensor (ExteriorAlgebra R L))
          (((⋀[R]^k L).subtype.rTensor M) p) :=
    LinearMap.congr_fun
      ((LinearMap.rTensor_comp_lTensor (⋀[R]^k L) (⋀[R]^k L).subtype f.toLinearMap).trans
        (LinearMap.lTensor_comp_rTensor (⋀[R]^k L) (⋀[R]^k L).subtype f.toLinearMap).symm) p
  apply LinearMap.ext
  intro p
  apply DirectSum.subtype_rTensor_injective (fun k : ℕ => ⋀[R]^k L) N n
  change ((⋀[R]^n L).subtype.rTensor N)
      ((f.toLinearMap.lTensor (⋀[R]^n L)) (coefficientDifferential R L M n p)) =
    ((⋀[R]^n L).subtype.rTensor N)
      (coefficientDifferential R L N n ((f.toLinearMap.lTensor (⋀[R]^(n + 1) L)) p))
  rw [hinclusion, coefficientDifferential_inclusion_apply,
    coefficientDifferential_inclusion_apply, hinclusion]
  simpa only [LinearMap.lTensor_def] using
    coefficientBoundary_naturality_apply R L M f
      (((⋀[R]^(n + 1) L).subtype.rTensor M) p)

end Naturality

section Maps

-- Native chain maps live in one ModuleCat universe. The preceding linear-map
-- naturality theorem retains independent universes.
variable {N P : Type w} [AddCommGroup N] [Module R N]
  [LieRingModule L N] [LieModule R L N]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For an R-Lie module map f:M→N with M,N in one coefficient
universe w, the maps id_{Λ^nL}⊗f form a chain map
C_*(L,M)→C_*(L,N) at height max{u,v,w}. -/
def coefficientComplexMap (f : M →ₗ⁅R,L⁆ N) :
    coefficientComplex R L M ⟶ coefficientComplex R L N :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (f.toLinearMap.lTensor (⋀[R]^n L)))
    (fun n => by
      simp only [coefficientComplex_d_succ]
      exact congrArg ModuleCat.ofHom (coefficientDifferential_naturality R L M f n).symm)

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For coefficients in a common universe, the degree-n component
of the chain map induced by f:M→N is id_{Λ_R^nL}⊗f. -/
@[simp]
theorem coefficientComplexMap_f (f : M →ₗ⁅R,L⁆ N) (n : ℕ) :
    (coefficientComplexMap R L M f).f n =
      ModuleCat.ofHom (f.toLinearMap.lTensor (⋀[R]^n L)) :=
  rfl

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For a coefficient Lie-module map f:M→N in the common
coefficient universe, the chain map sends a⊗m to a⊗f(m). -/
theorem coefficientComplexMap_f_tmul (f : M →ₗ⁅R,L⁆ N) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    ((coefficientComplexMap R L M f).f n).hom (a ⊗ₜ[R] m) = a ⊗ₜ[R] f m := by
  change f.toLinearMap.lTensor (⋀[R]^n L) (a ⊗ₜ[R] m) = a ⊗ₜ[R] f m
  simp only [LinearMap.lTensor_tmul, LieModuleHom.coe_toLinearMap]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
The coefficient chain map induced by id_M is the identity
of C_*(L,M). -/
@[simp]
theorem coefficientComplexMap_id :
    coefficientComplexMap R L M (LieModuleHom.id : M →ₗ⁅R,L⁆ M) =
      𝟙 (coefficientComplex R L M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext' (R := R)
  intro a m
  change ((coefficientComplexMap R L M (LieModuleHom.id : M →ₗ⁅R,L⁆ M)).f n).hom
    (a ⊗ₜ[R] m) = a ⊗ₜ[R] m
  rw [coefficientComplexMap_f_tmul, LieModuleHom.id_apply]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For coefficient Lie-module maps f:M→N and g:N→P,
with all coefficients in one universe, the chain maps satisfy
C(g)C(f)=C(g∘f). -/
@[simp]
theorem coefficientComplexMap_comp (f : M →ₗ⁅R,L⁆ N) (g : N →ₗ⁅R,L⁆ P) :
    coefficientComplexMap R L M f ≫ coefficientComplexMap R L N g =
      coefficientComplexMap R L M (g.comp f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext' (R := R)
  intro a m
  change ((coefficientComplexMap R L N g).f n).hom
      (((coefficientComplexMap R L M f).f n).hom (a ⊗ₜ[R] m)) =
    ((coefficientComplexMap R L M (g.comp f)).f n).hom (a ⊗ₜ[R] m)
  rw [coefficientComplexMap_f_tmul, coefficientComplexMap_f_tmul,
    coefficientComplexMap_f_tmul, LieModuleHom.comp_apply]

end Maps

end ChevalleyEilenberg
