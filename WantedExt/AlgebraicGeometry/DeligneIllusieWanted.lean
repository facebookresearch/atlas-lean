/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

/-!
# The Deligne–Illusie decomposition over `F_p`

Let `X` be a smooth scheme of pure relative dimension `d < p` over `F_p` which lifts to a smooth
scheme over `W₂(F_p)`. Deligne and Illusie proved that the de Rham complex `F_* Ω^•_{X/F_p}` is
decomposable: it is isomorphic, in the derived category of `𝒪_X`-modules, to the direct sum of
its cohomology sheaves `Ω^i_{X/F_p}` (by the Cartier isomorphism) placed in degrees `i`.

Over `F_p` the Frobenius twist `X'` of `X` is `X` itself and the relative Frobenius is the
absolute Frobenius, so `F_*` restricts scalars along `a ↦ a^p` (see
`MathlibExt.AlgebraicGeometry.PrimeFieldDeRham`). The lift is a smooth scheme `Y` over
`W₂(F_p)` whose special fibre, along the reduction `W₂(F_p) → F_p`, is `X`.

## References

* P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987), 247–270, Théorème 2.1 and Corollaire 2.2.
* P. Achinger, J. Suh, *Some refinements of the Deligne–Illusie theorem*, Algebra Number Theory 17
  (2023), §1A, https://msp.org/ant/2023/17-2/ant-v17-n2-p06-p.pdf
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeligneIllusie

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

attribute [local instance] HasDerivedCategory.standard

/-- **Deligne–Illusie** over $\mathbb{F}_p$: let $p$ be a prime and $X$ an $\mathbb{F}_p$-scheme
that is smooth of relative dimension $d < p$, with a smooth $W_2(\mathbb{F}_p)$-scheme $Y$ and a
morphism $j : X \to Y$ exhibiting $X$ as the special fibre
$Y \times_{W_2(\mathbb{F}_p)} \mathbb{F}_p$. Then there is an isomorphism
$F_* \Omega^\bullet_{X/\mathbb{F}_p} \cong \bigoplus_{i=0}^{d} \Omega^i_{X/\mathbb{F}_p}[-i]$ in the
derived category of $\mathcal{O}_X$-modules. -/
public theorem_wanted deligneIllusie
    (p : ℕ) [Fact p.Prime] (X : PrimeFieldScheme p) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (hd : d < p)
    (Y : Over (Spec (CommRingCat.of.{0}
      (TruncatedWittVector p 2 (ZMod p)))))
    [Smooth Y.hom]
    (j : X.left ⟶ Y.left)
    (hfibre : IsPullback j X.hom Y.hom
      (Spec.map (CommRingCat.ofHom (wittReduction p)))) :
    Nonempty ((Differential.deRham p X).derived ≅ ∐ fun i : Fin (d + 1) =>
      (DerivedCategory.singleFunctor X.left.Modules (i : ℤ)).obj
        (forms p X i))

end WantedExt.AlgebraicGeometry.DeligneIllusie
