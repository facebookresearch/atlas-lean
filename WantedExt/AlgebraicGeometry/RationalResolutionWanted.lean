/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RationalResolution
public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Rational singularities and Grauert–Riemenschneider vanishing

These requests use actual resolutions, their normalized structure maps,
canonical lines characterized by natural Serre duality, and actual higher
direct-image sheaves. Generic depth and surface-resolution facts already
in the public sources are not requested separately.

Independence of the resolution and Cohen–Macaulayness are stated for every
normal variety (integral, separated and of finite type). Grauert–Riemenschneider
vanishing is stated for proper varieties: there the resolution is proper over `k`,
so natural Serre duality pins its canonical line.

References: Grauert–Riemenschneider, *Verschwindungssätze für analytische
Kohomologiegruppen auf komplexen Räumen*, Invent. Math. 11 (1970), 263–292;
Kollár–Mori, *Birational Geometry of Algebraic Varieties*, Chapter 5.
Covered surface source: AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RationalResolutionWanted

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BirationalResolution
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies

universe u

/-- Rationality does not depend on the resolution: let $k$ be an algebraically closed field of
characteristic zero and $X$ a normal integral $k$-scheme that is separated, locally of finite type
and quasi-compact. If one resolution $f : Y \to X$ (a proper, locally projective, birational
morphism from a smooth integral $k$-scheme that is an isomorphism over every open subset of $X$
smooth over $k$) is rational, that is, $\mathcal{O}_X \to f_* \mathcal{O}_Y$ is an isomorphism and
$R^i f_* \mathcal{O}_Y = 0$ for $i > 0$, then every resolution of $X$ is rational. -/
theorem_wanted resolution_independence (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (hX : IsNormalIntegral X.left)
    (R T : ResolutionModel X) (hR : IsRationalResolution R) :
    IsRationalResolution T

/-- Rational singularities are Cohen–Macaulay: let $k$ be an algebraically closed field of
characteristic zero and $X$ a normal integral $k$-scheme that is separated, locally of finite type,
quasi-compact and locally Noetherian. If $X$ has a rational resolution $f : Y \to X$ (a proper,
locally projective, birational morphism from a smooth integral $k$-scheme that is an isomorphism
over every open subset of $X$ smooth over $k$, with $\mathcal{O}_X \to f_* \mathcal{O}_Y$ an
isomorphism and $R^i f_* \mathcal{O}_Y = 0$ for $i > 0$), then every local ring of $X$ is
Cohen–Macaulay (its depth equals its dimension). -/
theorem_wanted rational_isCohenMacaulay (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsLocallyNoetherian X.left]
    (hX : IsNormalIntegral X.left)
    (R : ResolutionModel X) (hR : IsRationalResolution R) :
    IsCohenMacaulayStalkwise X.left

/-- Grauert–Riemenschneider vanishing: let $k$ be an algebraically closed field of characteristic
zero, $X$ an integral proper $k$-scheme (not necessarily normal), $f : Y \to X$ a resolution (a
proper, locally projective, birational morphism from a smooth integral $k$-scheme that is an
isomorphism over every open subset of $X$ smooth over $k$) with $Y$ smooth of relative dimension $n$
over $k$, and $K$ a canonical line on $Y$: a line bundle with natural Serre duality isomorphisms
$\operatorname{Hom}(F, K) \cong H^n(Y, F)^\vee$ for all vector bundles $F$ on $Y$. Then
$R^i f_* K = 0$ for all $i > 0$. -/
theorem_wanted grauertRiemenschneider (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (R : ResolutionModel X) (n : ℕ)
    [SmoothOfRelativeDimension n R.source.hom]
    (K : R.source.left.Modules)
    (hK : SerreDualizingLine R.source.hom K n) :
    ∀ i : ℕ, 0 < i → IsZero (higherDirectImage R.morphism.left K i)

end WantedExt.AlgebraicGeometry.RationalResolutionWanted
