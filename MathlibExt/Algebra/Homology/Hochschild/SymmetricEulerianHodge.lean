/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianComplex
public import MathlibExt.Algebra.Homology.LocallyFiniteIdempotentImages
public import MathlibExt.Algebra.Homology.HomotopyEquivOnSplitImages

/-!
# A-linear Eulerian decompositions and normalization of their images

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an
A-module with compatible k-action. The raw coefficient complex C has
terms M ⊗[k] A^⊗n. Its normalized complex N has terms
M ⊗[k] (A/(k·1))^⊗n, where A/(k·1) is a k-module quotient.
Both are A-linear complexes, with A acting on the coefficient.

The Eulerian chain projectors e^(i) and their normalized counterparts
are orthogonal and complete: in degree n, they vanish for i > n and
sum to id over 0 ≤ i ≤ n. Their image inclusions give chain and homology
isomorphisms ⨁_i Im(e^(i)) ≅ C and ⨁_i Im(e_N^(i)) ≅ N.

The normalization q : C → N intertwines corresponding projectors.
Its restriction to each Eulerian image is a homotopy equivalence.
An inverse is obtained by including the normalized image, applying the
normalization section, and projecting to the raw image; the homotopies
are also restricted and projected. These statements require no
commutation premise for the unprojected section or homotopies.
All complexes lie in ModuleCat^max(u,v,w)(A), with independent worlds
for k, A and M.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, the ith raw Eulerian image complex is
Im(e_C^(i)) in the category of ℕ-indexed A-module chain complexes.
The coefficient action of A gives the raw terms M ⊗[k] A^⊗n
their A-module structure. -/
def algebraEulerianImageComplex (i : ℕ) : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraEulerianChainMap k A M i)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the ith normalized Eulerian image is
Im(e_N^(i)) on the normalized complex with terms
M ⊗[k] (A/(k·1))^⊗n. It is an A-module chain complex, with A acting
on the coefficient. -/
def algebraNormalizedEulerianImageComplex (i : ℕ) :
    ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraNormalizedEulerianChainMap k A M i)

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and a compatible A-module M, the degree-n component of the raw
Eulerian chain map e_C^(i) is zero whenever n < i. -/
theorem algebraEulerianChainMap_support (n i : ℕ) (hi : n < i) :
    (algebraEulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  simp only [algebraEulerianChainMap_f, ModuleCat.hom_zero]
  exact algebraEulerianOperator_outside k A M n i hi

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the degree-n component of the normalized
Eulerian chain map e_N^(i) is zero whenever n < i. -/
theorem algebraNormalizedEulerianChainMap_support (n i : ℕ) (hi : n < i) :
    (algebraNormalizedEulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  simp only [algebraNormalizedEulerianChainMap_f, ModuleCat.hom_zero]
  exact algebraNormalizedEulerianOperator_outside k A M n i hi

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and n ≥ 0, the raw degree-n Eulerian
components satisfy ∑_(i=0)^n e_(C,n)^(i) = id on
M ⊗[k] A^⊗n, as A-module morphisms. -/
theorem algebraEulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (algebraEulerianChainMap k A M i.val).f n) =
      𝟙 ((algebraRawComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, algebraEulerianChainMap_f]
  exact algebraEulerianOperator_sum k A M n

/-- For k a commutative ℚ-algebra, A a commutative k-algebra,
a compatible A-module M and n ≥ 0, the normalized Eulerian
components satisfy ∑_(i=0)^n e_(N,n)^(i) = id on
M ⊗[k] (A/(k·1))^⊗n, as A-module morphisms. -/
theorem algebraNormalizedEulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (algebraNormalizedEulerianChainMap k A M i.val).f n) =
      𝟙 ((algebraNormalizedChainComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, algebraNormalizedEulerianChainMap_f]
  exact algebraNormalizedEulerianOperator_sum k A M n

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, the raw image inclusions give the A-linear
chain isomorphism ⨁_(i∈ℕ) Im(e_C^(i)) ≅ C.
Local finiteness follows from the support bound i ≤ n in degree n. -/
def algebraHodgeComplexIso :
    (∐ (fun i : ℕ => algebraEulerianImageComplex k A M i)) ≅ algebraRawComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (algebraRawComplex k A M) (algebraEulerianChainMap k A M)
    (algebraEulerianChainMap_comp k A M) id
    (algebraEulerianChainMap_support k A M) (algebraEulerianChainMap_sum k A M)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the forward map of
⨁_i Im(e_C^(i)) ≅ C has ith component the categorical image
inclusion Im(e_C^(i)) → C. -/
theorem algebraHodgeComplexIso_hom :
    (algebraHodgeComplexIso k A M).hom =
      Sigma.desc (fun i => image.ι (algebraEulerianChainMap k A M i)) := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, the normalized image inclusions give
the A-linear chain isomorphism ⨁_(i∈ℕ) Im(e_N^(i)) ≅ N.
Only i ≤ n can contribute to a degree-n component. -/
def algebraNormalizedHodgeComplexIso :
    (∐ (fun i : ℕ => algebraNormalizedEulerianImageComplex k A M i)) ≅
      algebraNormalizedChainComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (algebraNormalizedChainComplex k A M) (algebraNormalizedEulerianChainMap k A M)
    (algebraNormalizedEulerianChainMap_comp k A M) id
    (algebraNormalizedEulerianChainMap_support k A M) (algebraNormalizedEulerianChainMap_sum k A M)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra,
a compatible A-module M and n ≥ 0, the raw Eulerian images give
the A-module isomorphism ⨁_(i∈ℕ) H_n(Im(e_C^(i))) ≅ H_n(C).
Its maps are induced by the image inclusions and finite projectors. -/
def algebraHodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (algebraEulerianImageComplex k A M i).homology n)) ≅
      (algebraRawComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (algebraRawComplex k A M) (algebraEulerianChainMap k A M)
    (algebraEulerianChainMap_comp k A M) id
    (algebraEulerianChainMap_support k A M) (algebraEulerianChainMap_sum k A M) n

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and n ≥ 0, there is an A-module isomorphism
⨁_(i∈ℕ) H_n(Im(e_N^(i))) ≅ H_n(N), induced by the complete locally
finite family of normalized Eulerian projectors. -/
def algebraNormalizedHodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (algebraNormalizedEulerianImageComplex k A M i).homology n)) ≅
      (algebraNormalizedChainComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (algebraNormalizedChainComplex k A M) (algebraNormalizedEulerianChainMap k A M)
    (algebraNormalizedEulerianChainMap_comp k A M) id
    (algebraNormalizedEulerianChainMap_support k A M) (algebraNormalizedEulerianChainMap_sum k A M) n

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the forward raw Hodge homology map has
ith component H_n(Im(e_C^(i)) → C), the homology morphism of
the raw Eulerian image inclusion. -/
theorem algebraHodgeHomologyIso_hom (n : ℕ) :
    (algebraHodgeHomologyIso k A M n).hom =
      Sigma.desc (fun i => HomologicalComplex.homologyMap
        (image.ι (algebraEulerianChainMap k A M i)) n) := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and i ≥ 0, normalization induces a chain
homotopy equivalence Im(e_C^(i)) ≃ Im(e_N^(i)).
The forward map is inclusion, normalization and image projection;
the inverse and homotopies are obtained by restricting and projecting
the normalization section and homotopies. -/
def algebraEulerianImageNormalizationHomotopyEquiv (i : ℕ) :
    HomotopyEquiv (algebraEulerianImageComplex k A M i)
      (algebraNormalizedEulerianImageComplex k A M i) :=
  HomologicalComplex.homotopyEquivOnSplitImages
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId
    (image.ι (algebraEulerianChainMap k A M i)) (factorThruImage (algebraEulerianChainMap k A M i))
    (image_ι_factorThruImage_of_idempotent _
      (by
        have h := algebraEulerianChainMap_comp k A M i i
        simp only [ite_true] at h
        exact h))
    (image.ι (algebraNormalizedEulerianChainMap k A M i))
    (factorThruImage (algebraNormalizedEulerianChainMap k A M i))
    (image_ι_factorThruImage_of_idempotent _
      (by
        have h := algebraNormalizedEulerianChainMap_comp k A M i i
        simp only [ite_true] at h
        exact h))
    (by
      change (factorThruImage (algebraEulerianChainMap k A M i) ≫
          image.ι (algebraEulerianChainMap k A M i)) ≫ algebraNormalizationProjection k A M =
        algebraNormalizationProjection k A M ≫
          (factorThruImage (algebraNormalizedEulerianChainMap k A M i) ≫
            image.ι (algebraNormalizedEulerianChainMap k A M i))
      exact (congrArg (fun t => t ≫ algebraNormalizationProjection k A M)
        (image.fac (algebraEulerianChainMap k A M i))).trans
        ((algebraNormalizationProjection_eulerian k A M i).symm.trans
          (congrArg (fun t => algebraNormalizationProjection k A M ≫ t)
            (image.fac (algebraNormalizedEulerianChainMap k A M i)).symm)))

/-- For k a commutative ℚ-algebra, A a commutative k-algebra,
a compatible A-module M and i ≥ 0, the forward map of the
Eulerian image normalization equivalence is
Im(e_C^(i)) → C → N → Im(e_N^(i)),
in that order: image inclusion, normalization projection, then
factorization of the normalized Eulerian projector. -/
theorem algebraEulerianImageNormalizationHomotopyEquiv_hom (i : ℕ) :
    (algebraEulerianImageNormalizationHomotopyEquiv k A M i).hom =
      image.ι (algebraEulerianChainMap k A M i) ≫ algebraNormalizationProjection k A M ≫
        factorThruImage (algebraNormalizedEulerianChainMap k A M i) := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and n,i ≥ 0, normalization induces
H_n(Im(e_C^(i))) ≅ H_n(Im(e_N^(i))) as A-modules.
The isomorphism is induced by the chain homotopy equivalence on
the corresponding image complexes. -/
def algebraEulerianImageNormalizationHomologyIso (n i : ℕ) :
    (algebraEulerianImageComplex k A M i).homology n ≅
      (algebraNormalizedEulerianImageComplex k A M i).homology n :=
  (algebraEulerianImageNormalizationHomotopyEquiv k A M i).toHomologyIso n

end ModuleCat.Algebra.Hochschild.Symmetric
