/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Module.Torsion.TateModule
public import MathlibExt.AlgebraicGeometry.AbelianSchemes
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public noncomputable section

/-!
# The first `ℓ`-adic cohomology of an abelian variety and its Tate module

For an abelian variety `A` over a field `k`, a separable closure `K` of `k` and a prime `ℓ`
different from the characteristic of `k`, the first `ℓ`-adic cohomology group
`H¹(A_K, ℤ_ℓ)` is isomorphic to `Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`, compatibly with the actions of
`Gal(K/k)`.

Here `A` is an abelian scheme over `Spec k`
(`MathlibExt.AlgebraicGeometry.AbelianSchemes.AbelianScheme`), and `T_ℓ A` is the Tate module
(`_root_.TateModule`) of the group `A(K)` of `K`-points of `A`, the morphisms `Spec K ⟶ A` over
`Spec k` with the group law of `A`. The cohomology `H¹(A_K, ℤ_ℓ)` is the cohomology of the
pro-étale sheaf `C(-, ℤ_ℓ)` of `ℤ_ℓ`-modules on `A_K = A ×_k Spec K`
(`MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality.Cohomology`), which computes the
`ℓ`-adic étale cohomology `lim H¹(A_K, ℤ/ℓⁿ)` of the source for such `A`. An automorphism `σ` of
`K` over `k` acts on it by inverse image along `id_A × Spec σ`
(`MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators.galoisSchemeOperator`), and on `A(K)`
by `P ↦ Spec σ ≫ P`, which on coordinates applies `σ`.

## References

* J. S. Milne, *Abelian Varieties* (v2.0, 2008), Part I, Theorem 12.1(a), p. 55, and
  Remark 12.5, p. 56, <https://www.jmilne.org/math/CourseNotes/AV.pdf>.
* B. Bhatt and P. Scholze, *The pro-étale topology for schemes* (2015), §5.6 and §6.8, for the
  comparison of pro-étale cohomology with `C(-, ℤ_ℓ)` coefficients and `ℓ`-adic étale cohomology.
-/

namespace WantedExt.AlgebraicGeometry.AbelianVarietyTateDualityWanted

open CategoryTheory CategoryTheory.MonObj
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

universe u

/-- **The ℓ-adic H¹ of an abelian variety is the dual of its Tate module, Galois-equivariantly.**
Let $k$ be a field, $K$ a separable closure of $k$, $\ell$ a prime different from the
characteristic of $k$, and $A$ an abelian variety over $k$. Write $A(K)$ for the group of
$K$-points of $A$ and $T_\ell A = \varprojlim_n A(K)[\ell^n]$ for its Tate module. Then there is a
$\mathbb{Z}_\ell$-linear isomorphism
$$\varphi \colon H^1(A_K, \mathbb{Z}_\ell) \xrightarrow{\ \sim\ }
  \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell)$$
compatible with the actions of $\operatorname{Gal}(K/k)$: for every $\sigma$, every
$x \in H^1(A_K, \mathbb{Z}_\ell)$ and every $t \in T_\ell A$,
$\varphi(\sigma x)(\sigma t) = \varphi(x)(t)$, that is,
$\varphi(\sigma x) = \varphi(x) \circ \sigma^{-1}$.

Here $H^1(A_K, \mathbb{Z}_\ell)$ is the cohomology of the pro-étale sheaf
$C(-, \mathbb{Z}_\ell)$ on $A_K = A \times_k \operatorname{Spec} K$, and $\sigma$ acts on it by
inverse image along $\mathrm{id}_A \times \operatorname{Spec} \sigma$. On $T_\ell A$, $\sigma$
acts through the induced map of Tate modules (`TateModule.map`) of any additive map $g$ of
$A(K)$ with $g(P) = \operatorname{Spec} \sigma \gg P$ for all $P$; exactly one such $g$ exists,
the action of $\sigma$ on points.

This is Milne, *Abelian Varieties* (v2.0, 2008), Theorem 12.1(a), p. 55, with the Galois
compatibility of Remark 12.5, p. 56, in degree one; with $K = k$ separably closed it is
Theorem 12.1(a), stated through the existence of an isomorphism rather than the canonical one. -/
public theorem_wanted h1_linearEquiv_dual_tateModule
    (ℓ : ℕ) [Fact ℓ.Prime] (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosure k K] (A : AbelianScheme (Spec (.of k))) (hℓ : ℓ ≠ ringChar k) :
    ∃ φ : Cohomology ℤ_[ℓ] (geometricFibre A.model K)
          (continuousModuleSheaf ℤ_[ℓ] (ULift.{u + 1} ℤ_[ℓ]) (geometricFibre A.model K)) 1
        ≃ₗ[ℤ_[ℓ]] Module.Dual ℤ_[ℓ] (TateModule ℓ (Additive (A.Points (Over.mk (fieldMap k K))))),
      ∀ (σ : K ≃ₐ[k] K)
        (g : Additive (A.Points (Over.mk (fieldMap k K))) →+
          Additive (A.Points (Over.mk (fieldMap k K)))),
        (∀ P, (Additive.toMul (g P)).left =
          Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ (Additive.toMul P).left) →
        ∀ x t, φ (continuousCohomologyPullback ℤ_[ℓ] (ULift.{u + 1} ℤ_[ℓ])
            (galoisSchemeOperator A.model K σ) 1 x)
            (MathlibExt.Algebra.Module.Torsion.TateModule.map g t) = φ x t

end WantedExt.AlgebraicGeometry.AbelianVarietyTateDualityWanted
