/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of a finite separable field extension to a separably closed field

For a finite separable field extension `L / K` and a separably closed field
`Ω` extending `K`, the base change `Ω ⊗[K] L` splits as a product of copies
of `Ω` indexed by the `K`-algebra homomorphisms `L →ₐ[K] Ω`, with
`1 ⊗ β` sent to the vector `(σ β)_σ`. The tensor factors are ordered
opposite to the source's `L ⊗[K] Ω` formulation. This is the field case of ATLAS
`NumberTheoryI` Proposition 4.43 (Section 4.2,
`v1/Atlas/NumberTheoryI/targets.yaml`); the book states it for finite étale
`K`-algebras, which are finite products of finite separable field
extensions. The proof adapts
`v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean`.

Mathlib's `Algebra.FormallyEtale.equivPiOfIsSepClosed` gives a related
splitting for an étale algebra over a separably closed field, indexed by its
prime spectrum; the statement here is indexed directly by the embeddings and
comes with the explicit evaluation formula.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsSepClosed Ω]

/-- **Number of embeddings into a separably closed field.** Let $L/K$ be a finite separable
field extension and let $\Omega$ be a separably closed field that is a $K$-algebra. Then the
number of $K$-algebra homomorphisms $L \to \Omega$ equals the degree $[L : K]$. -/
theorem algHom_card_eq_finrank_of_isSepClosed :
    Fintype.card (L →ₐ[K] Ω) = Module.finrank K L :=
  AlgHom.card_of_splits K L Ω fun x =>
    IsSepClosed.splits_codomain (minpoly K x)
      (Algebra.IsSeparable.isSeparable K x)

/-- **Evaluation of embeddings at an element.** Let $L/K$ be a finite separable field
extension, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. The
evaluation map is the $K$-algebra homomorphism from $L$ to the algebra of functions
$\mathrm{Hom}_K(L, \Omega) \to \Omega$ sending $l \in L$ to the function
$\sigma \mapsto \sigma(l)$. -/
def sepClosedEvalAlgHom : L →ₐ[K] ((L →ₐ[K] Ω) → Ω) where
  toFun l σ := σ l
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp
  commutes' := by intro r; ext σ; simp

/-- **Evaluation map on the base change to a separably closed field.** Let $L / K$ be a
finite separable field extension and let $\Omega$ be a separably closed field extension of
$K$. This is the homomorphism of $\Omega$-algebras from $\Omega \otimes_K L$ to the algebra
of functions from the set of $K$-algebra homomorphisms $L \to \Omega$ to $\Omega$, which
sends each pure tensor $\omega \otimes l$ to the function $\sigma \mapsto \omega \, \sigma(l)$. -/
def sepClosedTensorHom : (Ω ⊗[K] L) →ₐ[Ω] ((L →ₐ[K] Ω) → Ω) :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Ω _)
    (sepClosedEvalAlgHom K L Ω)

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsSepClosed Ω] in
/-- **Dedekind independence of embeddings.** Let $K$, $L$ and $\Omega$ be fields such that $L$
and $\Omega$ are $K$-algebras. Then the $K$-algebra homomorphisms $L \to \Omega$, viewed as
functions $L \to \Omega$, are linearly independent over $\Omega$.

This is an instance of Dedekind's theorem on the linear independence of characters. -/
theorem algHom_linearIndependent :
    LinearIndependent Ω (fun (σ : L →ₐ[K] Ω) (l : L) => σ l) :=
  (linearIndependent_monoidHom L Ω).comp
    (fun σ => AlgHom.toRingHom σ |>.toMonoidHom)
    (fun _ _ heq => AlgHom.ext (MonoidHom.ext_iff.mp heq))

/-- **Embeddings evaluated on a basis.** Let $L/K$ be a finite separable field extension of
degree $n$, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. Let
$b_1, \dots, b_n$ be a fixed basis of $L$ over $K$ (one particular basis chosen once and for
all, not an arbitrary one). Then the $n$ functions $\mathrm{Hom}_K(L, \Omega) \to \Omega$ given
by $\varphi \mapsto \varphi(b_i)$, for $i = 1, \dots, n$, are linearly independent over
$\Omega$. -/
theorem column_functions_linearIndependent :
    LinearIndependent Ω
      (fun (i : Fin (Module.finrank K L)) (φ : L →ₐ[K] Ω) =>
        φ (Module.finBasis K L i)) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [← (span_flip_eq_top_iff_linearIndependent).mpr
      (algHom_linearIndependent K L Ω)]
    apply Submodule.span_le.mpr
    intro f ⟨l, hl⟩
    rw [← hl]
    set b := Module.finBasis K L
    have heq : (flip (fun (σ : L →ₐ[K] Ω) (l : L) => σ l)) l =
        ∑ i, (algebraMap K Ω (b.repr l i)) •
          (fun (φ : L →ₐ[K] Ω) => φ (b i)) := by
      ext φ
      simp only [flip, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => rw [← b.sum_repr l, map_sum]
      congr 1
      ext i
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    rw [heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Fintype.card_fin, Module.finrank_pi_fintype, Finset.sum_const,
      Module.finrank_self,
      smul_eq_mul, mul_one, Finset.card_univ]
    exact (algHom_card_eq_finrank_of_isSepClosed K L Ω).symm

/-- **Injectivity of the evaluation homomorphism.** Let $L/K$ be a finite separable field
extension, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. Then the
evaluation homomorphism of $\Omega$-algebras from $\Omega \otimes_K L$ to the algebra of
functions $\mathrm{Hom}_K(L, \Omega) \to \Omega$, which sends $\omega \otimes l$ to the function
$\sigma \mapsto \omega\, \sigma(l)$, is injective. -/
theorem sepClosedTensorHom_injective :
    Function.Injective (sepClosedTensorHom K L Ω) := by
  set bΩ := Algebra.TensorProduct.basis Ω (Module.finBasis K L)
  apply LinearMap.injective_of_linearIndependent
    (f := (sepClosedTensorHom K L Ω).toLinearMap)
    (v := bΩ) (hv := bΩ.span_eq)
  have hcomp : (⇑(sepClosedTensorHom K L Ω).toLinearMap ∘ ⇑bΩ) =
      (fun (i : Fin (Module.finrank K L)) (φ : L →ₐ[K] Ω) =>
        φ (Module.finBasis K L i)) := by
    ext i φ
    simp [bΩ, Function.comp, AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.basis_apply, sepClosedTensorHom,
      Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, sepClosedEvalAlgHom]
  rw [hcomp]
  exact column_functions_linearIndependent K L Ω

/-- **Dimensions of the two sides of the splitting.** Let $L/K$ be a finite separable field
extension, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. Then the
base change $\Omega \otimes_K L$ and the space of functions $\mathrm{Hom}_K(L, \Omega) \to \Omega$
have the same dimension as vector spaces over $\Omega$.

Both dimensions equal the degree $[L : K]$. -/
theorem finrank_tensor_eq_finrank_pi_of_isSepClosed :
    Module.finrank Ω (Ω ⊗[K] L) = Module.finrank Ω ((L →ₐ[K] Ω) → Ω) := by
  rw [Module.finrank_baseChange, Module.finrank_pi_fintype, Finset.sum_const,
    Module.finrank_self, smul_eq_mul, mul_one, Finset.card_univ,
    algHom_card_eq_finrank_of_isSepClosed]

/-- **Surjectivity of the evaluation homomorphism.** Let $L/K$ be a finite separable field
extension, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. Then the
evaluation homomorphism of $\Omega$-algebras from $\Omega \otimes_K L$ to the algebra of
functions $\mathrm{Hom}_K(L, \Omega) \to \Omega$, which sends $\omega \otimes l$ to the function
$\sigma \mapsto \omega\, \sigma(l)$, is surjective.

This follows from injectivity, since both sides have dimension $[L : K]$ over $\Omega$. -/
theorem sepClosedTensorHom_surjective :
    Function.Surjective (sepClosedTensorHom K L Ω) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tensor_eq_finrank_pi_of_isSepClosed K L Ω)
    (f := (sepClosedTensorHom K L Ω).toLinearMap)).mp
    (sepClosedTensorHom_injective K L Ω)

/-- **Bijectivity of the evaluation homomorphism.** Let $L/K$ be a finite separable field
extension, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. Then the
evaluation homomorphism of $\Omega$-algebras from $\Omega \otimes_K L$ to the algebra of
functions $\mathrm{Hom}_K(L, \Omega) \to \Omega$, which sends $\omega \otimes l$ to the function
$\sigma \mapsto \omega\, \sigma(l)$, is bijective. -/
theorem sepClosedTensorHom_bijective :
    Function.Bijective (sepClosedTensorHom K L Ω) :=
  ⟨sepClosedTensorHom_injective K L Ω, sepClosedTensorHom_surjective K L Ω⟩

/-- **Splitting of a separable extension over a separably closed field.** Let $L/K$ be a
finite separable field extension, let $\Omega$ be a separably closed field that is a
$K$-algebra, and write $\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms
$L \to \Omega$. The splitting isomorphism is the isomorphism of $\Omega$-algebras from
$\Omega \otimes_K L$ onto the algebra $\Omega^{\mathrm{Hom}_K(L, \Omega)}$ of functions
$\mathrm{Hom}_K(L, \Omega) \to \Omega$ given by the evaluation homomorphism, which sends
$\omega \otimes l$ to the function $\sigma \mapsto \omega\, \sigma(l)$ and is bijective.

Source: ATLAS NumberTheoryI Proposition 4.43, field case; the book states it for finite
étale $K$-algebras. -/
noncomputable def sepClosedAlgEquiv : (Ω ⊗[K] L) ≃ₐ[Ω] ((L →ₐ[K] Ω) → Ω) :=
  AlgEquiv.ofBijective (sepClosedTensorHom K L Ω)
    (sepClosedTensorHom_bijective K L Ω)

/-- **The splitting isomorphism on pure tensors.** Let $L/K$ be a finite separable field
extension, let $\Omega$ be a separably closed field that is a $K$-algebra, and write
$\mathrm{Hom}_K(L, \Omega)$ for the set of $K$-algebra homomorphisms $L \to \Omega$. For all
$\omega \in \Omega$ and $l \in L$, the splitting isomorphism from $\Omega \otimes_K L$ onto the
algebra $\Omega^{\mathrm{Hom}_K(L, \Omega)}$ of functions $\mathrm{Hom}_K(L, \Omega) \to \Omega$
sends $\omega \otimes l$ to the function $\sigma \mapsto \omega\, \sigma(l)$. -/
theorem sepClosedAlgEquiv_apply (ω : Ω) (l : L) :
    sepClosedAlgEquiv K L Ω (ω ⊗ₜ[K] l) = fun σ => ω * σ l := by
  funext σ
  simp [sepClosedAlgEquiv, sepClosedTensorHom, Algebra.TensorProduct.lift_tmul,
    sepClosedEvalAlgHom]

end Algebra.TensorProduct
