/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PrimeToEllAlterations

@[expose] public noncomputable section

/-!
# Gabber prime-to-ell alterations of actual proper pairs

Authors: Ofer Gabber; Luc Illusie and Michael Temkin (Exposé X).
Editors: Luc Illusie, Yves Laszlo, Fabrice Orgogozo.
Source: Travaux de Gabber sur l'uniformisation locale et la cohomologie étale
des schémas quasi-excellents, Exposé X, Theorem 2.1, p. 149,
https://arxiv.org/abs/1207.3648.

This is a corollary of Theorem 2.1 for a perfect field and a proper integral
pair. It forgets the projectivity of the alteration, the quasi-projectivity
of its source and the auxiliary finite field extension of degree prime to
ell: over the perfect original field that extension is separable, so a
component of the source dominating the target is a smooth proper model over
the original field, with finite generic degree still prime to ell.
Existing ordinary alteration consequences, strict crossings predicates
and generic hypercover/cohomological-descent producers are toolbox.
-/

namespace WantedExt.AlgebraicGeometry.PrimeToEllAlterations

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.PrimeToEllAlterations

universe u

/-- **Gabber's prime-to-ℓ alteration.** Let $k$ be a perfect field, $\ell$ a prime invertible in
$k$, $X$ an integral proper $k$-scheme and $D$ an ideal sheaf on $X$ whose support is not all of
$X$. Then there are a smooth proper integral $k$-scheme $X'$ and a proper $k$-morphism
$f : X' \to X$ sending the generic point of $X'$ to that of $X$, such that the extension of function
fields is finite of degree prime to $\ell$ and the reduced inverse image of $D$ in $X'$ has strict
normal crossings. -/
public theorem_wanted gabber_primeToEllAlteration
    (k : Type u) [Field k] [PerfectField k] (ell : ℕ) [Fact ell.Prime]
    (ellInvertible : (ell : k) ≠ 0) (X : Over (Spec (.of k))) [IsIntegral X.left]
    [IsProper X.hom] (D : X.left.IdealSheafData)
    (boundaryNowhereDense : (D.support : Set X.left) ≠ Set.univ) :
    Nonempty (PrimeToEllAlteration X D ell)

end WantedExt.AlgebraicGeometry.PrimeToEllAlterations
