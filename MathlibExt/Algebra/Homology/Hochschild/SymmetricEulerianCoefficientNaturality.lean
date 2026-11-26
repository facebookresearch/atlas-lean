/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianProperImage

/-!
# Coefficient naturality of Eulerian projectors and first images

Let k be a commutative ℚ-algebra, A a commutative k-algebra, and M and
N be A-modules with compatible ground k-actions in the same carrier
world w. An A-linear map f : M → N gives coefficient maps on
C_n(A,M) = M ⊗[k] A^⊗n by applying f to the first factor and leaving
the algebra factors fixed.

These maps commute with every A-linear Eulerian projector e_n^(i)
and with the full first projector P_n = e_n^(0)+e_n^(1). The sections
from the proper both-positive shuffle quotient to the raw complex
are natural in f. Consequently the comparison between that quotient
and the categorical image of P is natural as an A-linear chain
isomorphism. The complexes lie in ModuleCat^max(u,v,w)(A), with
independent worlds of k, A and the coefficient modules; no coefficient
projectivity is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [SMulCommClass k A M] [SMulCommClass k A N]
  [IsScalarTower k A M] [IsScalarTower k A N]

section Eulerian

variable [Algebra ℚ k]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
compatible A-modules M and N and an A-linear map f : M → N, let
F_n = f ⊗ id_(A^⊗n). Then
F_n ∘ e_(M,n)^(i) = e_(N,n)^(i) ∘ F_n for all n,i ≥ 0,
as A-linear maps on the coefficient Hochschild terms. -/
theorem algebraEulerianOperator_coefficient (f : M →ₗ[A] N) (n i : ℕ) :
    (algebraCoefficientLevelMap k A f n).comp (algebraEulerianOperator k A M n i) =
      (algebraEulerianOperator k A N n i).comp (algebraCoefficientLevelMap k A f n) := by
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext'
  intro m x
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, algebraCoefficientLevelMap,
    algebraEulerianOperator, TensorProduct.AlgebraTensorModule.map_tmul,
    TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.id_apply]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
compatible A-modules M,N and f : M →ₗ[A] N, the coefficient map
F_n = f ⊗ id commutes with P_n = e_n^(0)+e_n^(1):
F_n ∘ P_(M,n) = P_(N,n) ∘ F_n for every n ≥ 0.
The weight-zero term is retained. -/
theorem algebraFirstEulerianOperator_coefficient (f : M →ₗ[A] N) (n : ℕ) :
    (algebraCoefficientLevelMap k A f n).comp (algebraFirstEulerianOperator k A M n) =
      (algebraFirstEulerianOperator k A N n).comp (algebraCoefficientLevelMap k A f n) := by
  simp only [algebraFirstEulerianOperator, LinearMap.comp_add, LinearMap.add_comp,
    algebraEulerianOperator_coefficient]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and f : M →ₗ[A] N between compatible coefficient modules, let
F_raw and F_+ be the induced maps on the raw and proper both-positive
shuffle quotient complexes. Their Eulerian sections s_M,s_N satisfy
s_N ∘ F_+ = F_raw ∘ s_M, from the M-quotient to the N-raw complex. -/
@[reassoc]
theorem algebraPositiveEulerianSection_coefficient (f : M →ₗ[A] N) :
    algebraPositiveCoefficientMap k A f ≫ algebraPositiveEulerianSection k A N =
      algebraPositiveEulerianSection k A M ≫ algebraRawCoefficientMap k A f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  exact (DFunLike.congr_fun (algebraFirstEulerianOperator_coefficient k A f n) x).symm

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
f : M →ₗ[A] N between compatible coefficient modules, the map
Im(P_M) → Im(P_N) includes the M-image in the raw complex, applies
the coefficient map f ⊗ id, and factors through the N-projector image.
Its endpoints are A-linear chain complexes at height max(u,v,w). -/
def algebraFirstEulerianImageCoefficientMap (f : M →ₗ[A] N) :
    algebraFirstEulerianImageComplex k A M ⟶ algebraFirstEulerianImageComplex k A N :=
  image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawCoefficientMap k A f ≫
    factorThruImage (algebraFirstEulerianChainMap k A N)

private theorem positiveSection_firstEulerian :
    algebraPositiveEulerianSection k A M ≫ algebraFirstEulerianChainMap k A M =
      algebraPositiveEulerianSection k A M := by
  rw [← algebraRawPositiveProjection_eulerianSection, ← Category.assoc,
    algebraPositiveEulerianSection_projection, Category.id_comp]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and f : M →ₗ[A] N between compatible coefficient modules, the
quotient-to-image isomorphisms χ_M,χ_N satisfy
χ_N ∘ F_+ = F_image ∘ χ_M.
The source is the proper both-positive shuffle quotient for M and
the target is Im(e_N^(0)+e_N^(1)); no projectivity of M or N is assumed. -/
@[reassoc]
theorem algebraFirstEulerianQuotientIso_coefficient (f : M →ₗ[A] N) :
    algebraPositiveCoefficientMap k A f ≫ (algebraFirstEulerianQuotientIso k A N).hom =
      (algebraFirstEulerianQuotientIso k A M).hom ≫ algebraFirstEulerianImageCoefficientMap k A f := by
  change algebraPositiveCoefficientMap k A f ≫
      (algebraPositiveEulerianSection k A N ≫ factorThruImage (algebraFirstEulerianChainMap k A N)) =
    (algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M)) ≫
      (image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawCoefficientMap k A f ≫
        factorThruImage (algebraFirstEulerianChainMap k A N))
  have h := congrArg
    (fun t : algebraPositiveQuotientComplex k A M ⟶ algebraRawComplex k A N =>
      t ≫ factorThruImage (algebraFirstEulerianChainMap k A N))
    (algebraPositiveEulerianSection_coefficient k A f)
  simp only [Category.assoc] at h
  simp only [Category.assoc, image.fac_assoc]
  rw [← Category.assoc (algebraPositiveEulerianSection k A M)
    (algebraFirstEulerianChainMap k A M), positiveSection_firstEulerian]
  exact h

end Eulerian

end ModuleCat.Algebra.Hochschild.Symmetric
