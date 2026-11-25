/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Quotient

@[expose] public section

open scoped TensorProduct

namespace Ideal

variable (K : Type*) [CommSemiring K]
variable (R : Type*) [CommRing R] [Algebra K R]
variable (ι : Type*) [Finite ι]
variable (I : ι → Ideal R)
variable (h : Pairwise fun i j => IsCoprime (I i) (I j))

/-- **Chinese remainder theorem as an algebra isomorphism.** Let $K$ be a commutative semiring,
let $R$ be a commutative ring that is a $K$-algebra, and let $(I_i)_{i \in \iota}$ be a family
of ideals of $R$ indexed by a finite type $\iota$ that are pairwise coprime, that is,
$I_i + I_j = R$ for $i \ne j$. Then the map sending the class of $r \in R$ to
$(r \bmod I_i)_{i \in \iota}$ is an isomorphism of $K$-algebras from $R / \bigcap_i I_i$ to
$\prod_i R / I_i$. -/
noncomputable def quotientInfAlgEquivPiQuotient :
    (R ⧸ ⨅ i, I i) ≃ₐ[K] (∀ i, R ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient I h) (fun c => by
    ext i
    rfl)

@[simp]
theorem quotientInfAlgEquivPiQuotient_mk (r : R) :
    quotientInfAlgEquivPiQuotient K R ι I h (Ideal.Quotient.mk _ r) =
      fun i ↦ Ideal.Quotient.mk (I i) r :=
  rfl

end Ideal

namespace AdjoinRoot

noncomputable def prodAlgEquiv {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (g : ι → Polynomial K)
    (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) :
    AdjoinRoot (∏ i, g i) ≃ₐ[K] (∀ i, AdjoinRoot (g i)) := by
  classical
  have hI : Pairwise fun i j => IsCoprime (Ideal.span {g i} : Ideal (Polynomial K))
      (Ideal.span {g j}) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff (g i) (g j)).mpr (hcop hij)
  exact (Ideal.quotientEquivAlgOfEq K (Ideal.iInf_span_singleton hcop).symm).trans
    (Ideal.quotientInfAlgEquivPiQuotient K (Polynomial K) ι
      (fun i => Ideal.span {g i}) hI)

@[simp]
theorem prodAlgEquiv_mk {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (g : ι → Polynomial K)
    (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) (p : Polynomial K) :
    prodAlgEquiv g hcop (AdjoinRoot.mk _ p) = fun i ↦ AdjoinRoot.mk (g i) p := by
  classical
  rfl

@[simp]
theorem prodAlgEquiv_root {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (g : ι → Polynomial K)
    (hcop : Pairwise (fun i j => IsCoprime (g i) (g j))) :
    prodAlgEquiv g hcop (AdjoinRoot.root _) = fun i ↦ AdjoinRoot.root (g i) := by
  classical
  change prodAlgEquiv g hcop (AdjoinRoot.mk _ Polynomial.X) =
    fun i ↦ AdjoinRoot.mk (g i) Polynomial.X
  exact prodAlgEquiv_mk g hcop Polynomial.X

noncomputable def tensorProductAlgEquiv {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (f : Polynomial K) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K');
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] AdjoinRoot (Polynomial.map (algebraMap K K') f) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
  have hcomp : ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* _).comp
      (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K) :
        Polynomial K →+* K' ⊗[K] Polynomial K) =
      Polynomial.mapRingHom (algebraMap K K') := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
        polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_C]
    · simp [Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
        polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_X]
  have h : Ideal.map ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* _)
      (Ideal.map (↑(Algebra.TensorProduct.includeRight (R := K) (A := K')
        (B := Polynomial K)) : Polynomial K →+* K' ⊗[K] Polynomial K)
        (Ideal.span {f})) =
      Ideal.span {Polynomial.map (algebraMap K K') f} := by
    rw [Ideal.map_map, hcomp, Ideal.map_span]
    simp
  exact (((Algebra.TensorProduct.commRight K K' (AdjoinRoot f)).symm.trans
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K' (Polynomial K) K'
      (Ideal.span {f}))).trans
    ((Ideal.quotientEquivAlg _ _ (polyEquivTensor' K K').symm rfl).trans
      (Ideal.quotientEquivAlgOfEq K' h)))

@[simp]
theorem tensorProductAlgEquiv_mk_tmul {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (f p : Polynomial K) (c : K') :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    tensorProductAlgEquiv f (AdjoinRoot.mk f p ⊗ₜ[K] c) =
      AdjoinRoot.mk (Polynomial.map (algebraMap K K') f)
        (c • Polynomial.map (algebraMap K K') p) := by
  rfl

@[simp]
theorem tensorProductAlgEquiv_root_tmul_one {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (f : Polynomial K) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    tensorProductAlgEquiv f (AdjoinRoot.root f ⊗ₜ[K] (1 : K')) =
      AdjoinRoot.root (Polynomial.map (algebraMap K K') f) := by
  change tensorProductAlgEquiv f (AdjoinRoot.mk f Polynomial.X ⊗ₜ[K] (1 : K')) =
    AdjoinRoot.mk (Polynomial.map (algebraMap K K') f) Polynomial.X
  rw [tensorProductAlgEquiv_mk_tmul, one_smul, Polynomial.map_X]

/-- **Base change of $K[X]/(f)$ along a factorization of $f$ over $K'$.** Let $K$ and $K'$
be fields with $K'$ a $K$-algebra, let $f \in K[X]$, and let $(g_i)_{i \in \iota}$ be a family
of irreducible polynomials in $K'[X]$, indexed by a finite type $\iota$, that are pairwise
non-associated and whose product $\prod_i g_i$ is associated (equal up to a unit) to the image
of $f$ in $K'[X]$. Then there is an isomorphism of $K'$-algebras
$$(K[X]/(f)) \otimes_K K' \cong \prod_{i \in \iota} K'[X]/(g_i),$$
where the tensor product is a $K'$-algebra through its right factor. For $p \in K[X]$ with
class $[p]$ in $K[X]/(f)$ and for $c \in K'$, it sends $[p] \otimes c$ to the family of the
classes of $c\,p$ modulo the $g_i$, with $p$ read in $K'[X]$.

Source: This is the algebraic decomposition in ATLAS N86, Corollary 4.39 of
[MIT 18.785 *Number Theory I*](https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/).
The corresponding upstream declaration is
[`TensorSplitting.adjoinRoot_tensor_algEquiv_prod` in
`v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean`, lines 146--160,
at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean#L146-L160).
There, `L` is presented as
`K[X] / (f)`, the extension `K' / K` is arbitrary, and the distinct irreducible
factors of `f` over `K'` are represented here by `g`, `hirr`, `hne`, and
`hprod`. The source assumes that `f` is irreducible and separable in order to
say that `L / K` is a finite separable field extension. Those assumptions are
not needed for this CRT decomposition of the explicitly presented algebra
`AdjoinRoot f`; accordingly, this theorem makes no stronger field or
finite-etale claim about its factors. -/
noncomputable def tensorProductAlgEquivPi {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] {ι : Type*} [Fintype ι] (f : Polynomial K)
    (g : ι → Polynomial K') (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j))
    (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i)) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f)
      (B := K');
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] (∀ i, AdjoinRoot (g i)) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f)
    (B := K')
  have hprime : ∀ i, Prime (g i) := fun i =>
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (hirr i)
  have hcop : Pairwise fun i j => IsCoprime (g i) (g j) := fun i j hij =>
    (hprime i).coprime_iff_not_dvd.mpr fun hdvd =>
      hne hij ((hprime i).associated_of_dvd (hprime j) hdvd)
  have hspan :
    Ideal.span ({Polynomial.map (algebraMap K K') f} : Set (Polynomial K')) =
      Ideal.span ({∏ i, g i} : Set (Polynomial K')) :=
    Ideal.span_singleton_eq_span_singleton.mpr hprod
  exact ((tensorProductAlgEquiv f).trans
    (Ideal.quotientEquivAlgOfEq K' hspan)).trans (prodAlgEquiv g hcop)

@[simp]
theorem tensorProductAlgEquivPi_mk_tmul_apply {K K' : Type*}
    [Field K] [Field K'] [Algebra K K'] {ι : Type*} [Fintype ι]
    (f p : Polynomial K) (g : ι → Polynomial K')
    (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j))
    (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i))
    (c : K') (i : ι) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    tensorProductAlgEquivPi f g hirr hne hprod
        (AdjoinRoot.mk f p ⊗ₜ[K] c) i =
      AdjoinRoot.mk (g i) (c • Polynomial.map (algebraMap K K') p) := by
  classical
  rfl

@[simp]
theorem tensorProductAlgEquivPi_root_tmul_one_apply {K K' : Type*}
    [Field K] [Field K'] [Algebra K K'] {ι : Type*} [Fintype ι]
    (f : Polynomial K) (g : ι → Polynomial K')
    (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j))
    (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i)) (i : ι) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    tensorProductAlgEquivPi f g hirr hne hprod
        (AdjoinRoot.root f ⊗ₜ[K] (1 : K')) i = AdjoinRoot.root (g i) := by
  change tensorProductAlgEquivPi f g hirr hne hprod
      (AdjoinRoot.mk f Polynomial.X ⊗ₜ[K] (1 : K')) i =
    AdjoinRoot.mk (g i) Polynomial.X
  rw [tensorProductAlgEquivPi_mk_tmul_apply, one_smul, Polynomial.map_X]

end AdjoinRoot
