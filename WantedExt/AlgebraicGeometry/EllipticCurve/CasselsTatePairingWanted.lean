/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Sha
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointGaloisAction

/-! # The Cassels–Tate pairing for elliptic curves over number fields

A statement-only request for Cassels' theorem: the Shafarevich–Tate group of an elliptic curve
over a number field carries an alternating pairing to $\mathbb{Q}/\mathbb{Z}$ that is
nondegenerate modulo the maximal divisible subgroup.

The Shafarevich–Tate group is Mathlib's `ContinuousCohomology.tateShafarevich` in degree one,
for the Galois module of points of $E$ over an algebraic closure $\bar K$ with the discrete
topology, localized at every place of $K$: the finite places through
`IsDedekindDomain.HeightOneSpectrum.adicCompletion` and the infinite places through
`NumberField.InfinitePlace.Completion`. As explained in the implementation notes of
`Mathlib.RepresentationTheory.Homological.ContCohomology.Sha`, the local groups there are
$H^1(G_{K_v}, E(\bar K))$ rather than $H^1(G_{K_v}, E(\bar K_v))$; at a finite place the map
between them is an isomorphism (Milne, *Arithmetic Duality Theorems*, 2nd ed., Remark I.3.10).
-/

namespace MetaMathlibExt

@[expose] public section

open scoped WeierstrassCurve.Affine

open NumberField IsDedekindDomain

variable {K : Type} [Field K]

open scoped Classical in
/-- **The Galois module of points of an elliptic curve.** Let $E$ be a Weierstrass curve over a
field $K$ with algebraic closure $\bar K$. This is the group $E(\bar K)$ of points of $E$ with
coordinates in $\bar K$, with the discrete topology, as a topological $\mathbb{Z}$-representation
of the absolute Galois group $G_K = \mathrm{Gal}(\bar K/K)$, which acts on the coordinates of
points. -/
noncomputable def ellipticPointsTopRep (E : WeierstrassCurve K) :
    TopRep ℤ (Field.absoluteGaloisGroup K) :=
  letI : TopologicalSpace (E⁄(AlgebraicClosure K)).Point := ⊥
  haveI : DiscreteTopology (E⁄(AlgebraicClosure K)).Point := ⟨rfl⟩
  TopRep.of (X := (E⁄(AlgebraicClosure K)).Point)
    (ContRepresentation.ofMonoidHom
      { toFun := fun σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
          ⟨(DistribSMul.toAddMonoidHom (E⁄(AlgebraicClosure K)).Point σ).toIntLinearMap,
            continuous_of_discreteTopology⟩
        map_one' := by
          ext P
          exact one_smul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) P
        map_mul' := fun σ τ => by
          ext P
          exact mul_smul (α := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) σ τ P })

/-- **The Shafarevich–Tate group of an elliptic curve over a number field.** Let $E$ be a
Weierstrass curve over a number field $K$ with algebraic closure $\bar K$. This is the group
$\text{Ш}(E/K)$ of classes in the continuous cohomology group $H^1(G_K, E(\bar K))$ whose
restriction to the absolute Galois group $G_{K_v}$ of the completion $K_v$ is zero for every
place $v$ of $K$, finite or infinite. -/
noncomputable def ellipticTateShafarevich [NumberField K] (E : WeierstrassCurve K) :
    AddSubgroup (continuousCohomology 1 (ellipticPointsTopRep E)) :=
  ContinuousCohomology.tateShafarevich
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) (ellipticPointsTopRep E) 1 ⊓
    ContinuousCohomology.tateShafarevich (fun w : InfinitePlace K => w.Completion)
      (ellipticPointsTopRep E) 1

/-- **Cassels' pairing on the Shafarevich–Tate group of an elliptic curve.** Let $E$ be an
elliptic curve over a number field $K$, and let $\text{Ш}(E)$ be its Shafarevich–Tate group.
There is a biadditive pairing
$\langle\,,\rangle \colon \text{Ш}(E) \times \text{Ш}(E) \to \mathbb{Q}/\mathbb{Z}$ that is
alternating, $\langle x, x\rangle = 0$ for all $x$, and that becomes nondegenerate after one
divides $\text{Ш}(E)$ by its maximal divisible subgroup: an element $x$ satisfies
$\langle x, y\rangle = 0$ for all $y$ if and only if $x$ lies in a divisible subgroup of
$\text{Ш}(E)$.

The divisible subgroups generate a divisible subgroup, so an element lies in some divisible
subgroup exactly when it lies in the maximal divisible subgroup. The kernel on the other side is
the same, since an alternating pairing is antisymmetric. The statement asserts that such a
pairing exists; it does not single out the pairing Cassels constructs.

Source: B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*,
Ann. of Math. (2) 150 (1999), 1109–1149, doi:10.2307/121064, Introduction, p. 1110, stating the
theorem of J. W. S. Cassels, *Arithmetic on curves of genus 1. IV. Proof of the
Hauptvermutung*, J. Reine Angew. Math. 211 (1962), 95–112. See also J. S. Milne,
*Arithmetic Duality Theorems*, 2nd ed. (2006), Theorem I.6.13 (a), p. 82, for the kernels, and
p. 81 for the alternating property. -/
theorem_wanted cassels_tate_pairing [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic] :
    ∃ b : ellipticTateShafarevich E →+ ellipticTateShafarevich E →+
        (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)),
      (∀ x, b x x = 0) ∧
        ∀ x, (∀ y, b x y = 0) ↔
          ∃ H : AddSubgroup (ellipticTateShafarevich E),
            (∀ h ∈ H, ∀ n : ℕ, n ≠ 0 → ∃ g ∈ H, n • g = h) ∧ x ∈ H

end

end MetaMathlibExt
