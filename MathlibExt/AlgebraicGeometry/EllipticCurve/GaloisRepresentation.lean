/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Algebra.Module.Torsion.Basic

attribute [local instance] Classical.decEq

@[expose] public section

/-!
# Galois action on `p`-torsion of an elliptic curve over `ℚ`

Infrastructure for the determinant identity of Gonzalez-Jimenez–Lozano-Robledo,
*Elliptic Curves with abelian division fields*, arXiv:1511.08578v2,
Math. Z. 283 (2016), DOI `10.1007/s00209-016-1623-z`.

Frozen source (path wrapped for line length), SHA-256
`33306eccf5fce60cc116e22c4227a9125a35370982c51473be94db57ef21abc9`:
`/data/users/akiezun/high_roi_mathlib/elementary_nt_gap_catalog_v1/`
`primary_sources/partC/determinant_abelian_arxiv_source/extracted/`
`gonzalez-lozano_v11b_arxiv.tex`.

This file builds the concrete natural Galois action on affine nonsingular points,
restricts it to the `p`-torsion subgroup (a `ZMod p`-module), packages each
automorphism as a linear equivalence, and defines the determinant character.
The proof of Proposition `prop-borel2` uses that the determinant of `ρ_{E,p}`
is the mod-`p` cyclotomic character; that identity itself is stated as a
`theorem_wanted` in `WantedExt.AlgebraicGeometry.EllipticCurve.CyclotomicDeterminant`
because Mathlib lacks the Weil pairing and the rank-two torsion theorem.
-/

namespace MetaMathlibExt

open WeierstrassCurve

/-- **Galois elements as automorphisms of $\overline{\mathbb{Q}}$.** Each element $\sigma$ of
the absolute Galois group $G_{\mathbb{Q}}$ of $\mathbb{Q}$ is regarded as the
$\mathbb{Q}$-algebra automorphism $\sigma$ of the algebraic closure $\overline{\mathbb{Q}}$ of
$\mathbb{Q}$. Since $G_{\mathbb{Q}}$ is by definition the group of $\mathbb{Q}$-algebra
automorphisms of $\overline{\mathbb{Q}}$, this map is the identity. -/
noncomputable def galAlgEquiv (σ : Field.absoluteGaloisGroup ℚ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

variable (W : Affine ℚ)

/-- **Galois action on the points of a Weierstrass curve.** Let $W$ be a Weierstrass curve over
$\mathbb{Q}$ and let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of $W$ with
coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity. For $\sigma$ in the absolute Galois group $G_{\mathbb{Q}}$, this is the homomorphism
of additive groups $W(\overline{\mathbb{Q}}) \to W(\overline{\mathbb{Q}})$ that sends the point
$(x, y)$ to $(\sigma(x), \sigma(y))$ and fixes the point at infinity.

For each natural number $p$, restricting this action to the $p$-torsion points gives the mod-$p$
Galois representation. -/
noncomputable def galPointHom (σ : Field.absoluteGaloisGroup ℚ) :
    Affine.Point (W.baseChange (AlgebraicClosure ℚ)) →+
      Affine.Point (W.baseChange (AlgebraicClosure ℚ)) :=
  Affine.Point.map (galAlgEquiv σ).toAlgHom

/-- **Galois elements as automorphisms of $\overline{\mathbb{Q}}$ respect products.** For all
$\sigma, \tau$ in the absolute Galois group $G_{\mathbb{Q}}$ of $\mathbb{Q}$, the
$\mathbb{Q}$-algebra automorphism of the algebraic closure $\overline{\mathbb{Q}}$ attached to
$\sigma\tau$ is the composite of the automorphisms attached to $\sigma$ and to $\tau$, with the
one attached to $\tau$ applied first.

The equality holds by definition. -/
@[simp] theorem galAlgEquiv_mul (σ τ : Field.absoluteGaloisGroup ℚ) :
    galAlgEquiv (σ * τ) = galAlgEquiv σ * galAlgEquiv τ := rfl

/-- **Galois elements as automorphisms of $\overline{\mathbb{Q}}$ respect inverses.** For every
$\sigma$ in the absolute Galois group $G_{\mathbb{Q}}$ of $\mathbb{Q}$, the $\mathbb{Q}$-algebra
automorphism of the algebraic closure $\overline{\mathbb{Q}}$ attached to $\sigma^{-1}$ is the
inverse of the automorphism attached to $\sigma$.

The equality holds by definition. -/
theorem galAlgEquiv_inv (σ : Field.absoluteGaloisGroup ℚ) :
    galAlgEquiv σ⁻¹ = (galAlgEquiv σ)⁻¹ := rfl

/-- **Galois automorphisms compose as algebra maps.** Let $\overline{\mathbb{Q}}$ be the algebraic
closure of $\mathbb{Q}$. For all $\sigma, \tau$ in the absolute Galois group $G_{\mathbb{Q}}$ of
$\mathbb{Q}$, the $\mathbb{Q}$-algebra homomorphism
$\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}$ underlying the product $\sigma\tau$ is the
composite $\sigma \circ \tau$ of the $\mathbb{Q}$-algebra homomorphisms underlying $\sigma$
and $\tau$. -/
theorem galToAlgHom_comp (σ τ : Field.absoluteGaloisGroup ℚ) :
    (galAlgEquiv (σ * τ)).toAlgHom =
      (galAlgEquiv σ).toAlgHom.comp (galAlgEquiv τ).toAlgHom := by
  ext x
  change (galAlgEquiv (σ * τ)) x = _
  rw [galAlgEquiv_mul, AlgEquiv.mul_apply]
  rfl

/-- **The identity acts trivially on points.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$
and let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of $W$ with coordinates in
the algebraic closure $\overline{\mathbb{Q}}$, together with the point at infinity. For $\sigma$
in the absolute Galois group $G_{\mathbb{Q}}$ and $P \in W(\overline{\mathbb{Q}})$, let
$\sigma \cdot P$ be the point obtained by applying $\sigma$ to the coordinates of $P$ (the point
at infinity is fixed). Then $1 \cdot P = P$ for every $P \in W(\overline{\mathbb{Q}})$, where
$1$ is the identity of $G_{\mathbb{Q}}$. -/
theorem galPointHom_apply_one (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
    galPointHom W 1 P = P := by
  cases P <;> rfl

/-- **The Galois action on points is compatible with multiplication.** Let $W$ be a Weierstrass
curve over $\mathbb{Q}$ and let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of
$W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity. For $\sigma$ in the absolute Galois group $G_{\mathbb{Q}}$ and
$P \in W(\overline{\mathbb{Q}})$, let $\sigma \cdot P$ be the point obtained by applying $\sigma$
to the coordinates of $P$ (the point at infinity is fixed). Then for all
$\sigma, \tau \in G_{\mathbb{Q}}$ and every $P \in W(\overline{\mathbb{Q}})$,
$(\sigma\tau) \cdot P = \sigma \cdot (\tau \cdot P)$. -/
theorem galPointHom_apply_mul (σ τ : Field.absoluteGaloisGroup ℚ)
    (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
    galPointHom W (σ * τ) P = galPointHom W σ (galPointHom W τ P) := by
  change Affine.Point.map _ P = Affine.Point.map _ (Affine.Point.map _ P)
  rw [galToAlgHom_comp, ← Affine.Point.map_map]

variable (p : ℕ)

/-- **The $p$-torsion subgroup.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$, let $p$ be a
natural number, and let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of $W$ with
coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at infinity.
The $p$-torsion subgroup $W[p]$ is the subgroup of points $P \in W(\overline{\mathbb{Q}})$ with
$pP = 0$.

When $W$ is an elliptic curve $E$, this is the group usually written $E[p]$. -/
noncomputable def torsionPts :=
  AddSubgroup.torsionBy (Affine.Point (W.baseChange (AlgebraicClosure ℚ))) (p : ℤ)

/-- The `ZMod p`-module structure on `p`-torsion points. -/
noncomputable instance instZModModule : Module (ZMod p) (torsionPts W p) :=
  AddSubgroup.torsionBy.zmodModule

/-- **Membership in the $p$-torsion subgroup.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$,
let $p$ be a natural number, let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of
$W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity, and let $W[p]$ be its $p$-torsion subgroup. A point $x \in W(\overline{\mathbb{Q}})$
lies in $W[p]$ if and only if $p x = 0$, where $p x$ is the sum of $p$ copies of $x$ and $0$ is
the point at infinity. -/
theorem mem_torsionPts_iff {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))} :
    x ∈ torsionPts W p ↔ p • x = 0 := by
  change x ∈ AddSubgroup.torsionBy _ _ ↔ _
  exact AddSubgroup.torsionBy.nsmul_iff

/-- **The Galois action preserves $p$-torsion points.** Let $W$ be a Weierstrass curve over
$\mathbb{Q}$, let $p$ be a natural number, let $W(\overline{\mathbb{Q}})$ be the group of
nonsingular points of $W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$,
together with the point at infinity, and let $W[p]$ be its subgroup of points $P$ with $pP = 0$.
For $\sigma$ in the absolute Galois group $G_{\mathbb{Q}}$ and $P \in W(\overline{\mathbb{Q}})$,
let $\sigma \cdot P$ be the point obtained by applying $\sigma$ to the coordinates of $P$ (the
point at infinity is fixed). Then for every $\sigma \in G_{\mathbb{Q}}$ and every $x \in W[p]$,
the point $\sigma \cdot x$ lies in $W[p]$. -/
theorem galPointHom_mem (σ : Field.absoluteGaloisGroup ℚ)
    {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))}
    (hx : x ∈ torsionPts W p) : galPointHom W σ x ∈ torsionPts W p := by
  rw [mem_torsionPts_iff] at hx ⊢
  rw [← map_nsmul]
  rw [hx, map_zero]

/-- **Galois action on $p$-torsion points.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$,
let $p$ be a natural number, let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of
$W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity, and let $W[p]$ be its subgroup of points $P$ with $pP = 0$. For $\sigma$ in the
absolute Galois group $G_{\mathbb{Q}}$, this is the homomorphism of additive groups
$W[p] \to W[p]$ that sends the point $(x, y)$ to $(\sigma(x), \sigma(y))$ and fixes the point at
infinity. -/
noncomputable def galTorsionHom (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p →+ torsionPts W p where
  toFun x := ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩
  map_zero' := by
    apply Subtype.ext
    change galPointHom W σ _ = _
    exact map_zero _
  map_add' := fun x y => by
    apply Subtype.ext
    change galPointHom W σ _ = _
    exact map_add _ _ _

/-- **Linear Galois action on $W[p]$.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$,
$p$ a natural number, $W(\overline{\mathbb{Q}})$ the group of nonsingular points of $W$ with
coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity, and $W[p]$ its $p$-torsion subgroup; it is a $\mathbb{Z}/p\mathbb{Z}$-module because
$p$ annihilates it. For $\sigma$ in the absolute Galois group $G_{\mathbb{Q}}$ of $\mathbb{Q}$,
this is the $\mathbb{Z}/p\mathbb{Z}$-linear map $W[p] \to W[p]$, $x \mapsto \sigma(x)$, where
$\sigma$ acts on points through their coordinates. -/
noncomputable def galLinearMap (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p →ₗ[ZMod p] torsionPts W p :=
  (galTorsionHom W p σ).toZModLinearMap p

/-- **The linear Galois action on $W[p]$ is the action on points.** Let $W$ be a Weierstrass
curve over $\mathbb{Q}$, $p$ a natural number, $W(\overline{\mathbb{Q}})$ the group of nonsingular
points of $W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the
point at infinity, and $W[p]$ its $p$-torsion subgroup. For every $\sigma$ in the absolute Galois
group $G_{\mathbb{Q}}$ of $\mathbb{Q}$ and every $x \in W[p]$, the image of $x$ under the
$\mathbb{Z}/p\mathbb{Z}$-linear action of $\sigma$ on $W[p]$ is the point $\sigma(x)$ given by the
Galois action of $\sigma$ on all of $W(\overline{\mathbb{Q}})$. -/
theorem galLinearMap_apply (σ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p σ x = ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩ :=
  rfl

/-- **The identity acts trivially on $W[p]$.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$,
$p$ a natural number, $W(\overline{\mathbb{Q}})$ the group of nonsingular points of $W$ with
coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity, and $W[p]$ its $p$-torsion subgroup. Under the $\mathbb{Z}/p\mathbb{Z}$-linear action
of the absolute Galois group of $\mathbb{Q}$ on $W[p]$, the identity element maps every
$x \in W[p]$ to $x$. -/
theorem galLinearMap_one_apply (x : torsionPts W p) :
    galLinearMap W p 1 x = x := by
  apply Subtype.ext
  change galPointHom W 1 x.val = x.val
  exact galPointHom_apply_one W x.val

/-- **The linear Galois action on $W[p]$ respects products.** Let $W$ be a Weierstrass curve
over $\mathbb{Q}$, $p$ a natural number, $W(\overline{\mathbb{Q}})$ the group of nonsingular
points of $W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the
point at infinity, and $W[p]$ its $p$-torsion subgroup. For $\sigma$ in the absolute Galois group
$G_{\mathbb{Q}}$ of $\mathbb{Q}$ and $x \in W[p]$, write $\sigma \cdot x$ for the image of $x$
under the $\mathbb{Z}/p\mathbb{Z}$-linear action of $\sigma$ on $W[p]$. Then for all
$\sigma, \tau \in G_{\mathbb{Q}}$ and every $x \in W[p]$,
$(\sigma\tau) \cdot x = \sigma \cdot (\tau \cdot x)$. -/
theorem galLinearMap_mul_apply (σ τ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p (σ * τ) x = galLinearMap W p σ (galLinearMap W p τ x) := by
  apply Subtype.ext
  change galPointHom W (σ * τ) x.val = galPointHom W σ (galPointHom W τ x.val)
  exact galPointHom_apply_mul W σ τ x.val

/-- **Galois automorphisms act bijectively on $W[p]$.** Let $W$ be a Weierstrass curve over
$\mathbb{Q}$, $p$ a natural number, $W(\overline{\mathbb{Q}})$ the group of nonsingular points of
$W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity, and $W[p]$ its $p$-torsion subgroup. For every $\sigma$ in the absolute Galois group
$G_{\mathbb{Q}}$ of $\mathbb{Q}$, the $\mathbb{Z}/p\mathbb{Z}$-linear map by which $\sigma$ acts
on $W[p]$ is bijective.

The action of $\sigma^{-1}$ is a two-sided inverse. -/
theorem galLinearMap_bijective (σ : Field.absoluteGaloisGroup ℚ) :
    Function.Bijective (galLinearMap W p σ) := by
  have hleft : Function.LeftInverse (galLinearMap W p σ⁻¹) (galLinearMap W p σ) := by
    intro x
    rw [← galLinearMap_mul_apply, inv_mul_cancel, galLinearMap_one_apply]
  have hright : Function.RightInverse (galLinearMap W p σ⁻¹) (galLinearMap W p σ) := by
    intro x
    rw [← galLinearMap_mul_apply, mul_inv_cancel, galLinearMap_one_apply]
  exact ⟨hleft.injective, hright.surjective⟩

/-- **Galois automorphisms as linear automorphisms of $W[p]$.** Let $W$ be a Weierstrass curve
over $\mathbb{Q}$, $p$ a natural number, $W(\overline{\mathbb{Q}})$ the group of nonsingular
points of $W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the
point at infinity, and $W[p]$ its $p$-torsion subgroup. For $\sigma$ in the absolute Galois group
$G_{\mathbb{Q}}$ of $\mathbb{Q}$, this is the $\mathbb{Z}/p\mathbb{Z}$-linear map
$x \mapsto \sigma(x)$ on $W[p]$, where $\sigma$ acts on points through their coordinates, viewed
as a linear automorphism of $W[p]$ (the map is bijective). -/
noncomputable def galLinearEquiv (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p ≃ₗ[ZMod p] torsionPts W p :=
  LinearEquiv.ofBijective _ (galLinearMap_bijective W p σ)

/-- **The mod-$p$ Galois representation.** Let $W$ be a Weierstrass curve over $\mathbb{Q}$, let
$p$ be a natural number, let $W(\overline{\mathbb{Q}})$ be the group of nonsingular points of $W$
with coordinates in the algebraic closure $\overline{\mathbb{Q}}$, together with the point at
infinity, and let $W[p]$ be its subgroup of points $P$ with $pP = 0$, viewed as a
$\mathbb{Z}/p\mathbb{Z}$-module. The mod-$p$ Galois representation is the group homomorphism
from the absolute Galois group $G_{\mathbb{Q}}$ to the group of $\mathbb{Z}/p\mathbb{Z}$-linear
automorphisms of $W[p]$ that sends $\sigma$ to the map $(x, y) \mapsto (\sigma(x), \sigma(y))$,
which fixes the point at infinity.

When $W$ is an elliptic curve $E$, this is the representation usually written $\rho_{E,p}$. -/
noncomputable def galRep :
    Field.absoluteGaloisGroup ℚ →* (torsionPts W p ≃ₗ[ZMod p] torsionPts W p) where
  toFun σ := galLinearEquiv W p σ
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change galLinearMap W p 1 x = _
    rw [galLinearMap_one_apply]
    rfl
  map_mul' := fun σ τ => by
    apply LinearEquiv.ext
    intro x
    change galLinearMap W p (σ * τ) x = _
    rw [galLinearMap_mul_apply]
    rfl

/-- **Determinant character of the mod-$p$ Galois representation.** Let $W$ be a Weierstrass
curve over $\mathbb{Q}$, let $p$ be a natural number, let $W(\overline{\mathbb{Q}})$ be the group
of nonsingular points of $W$ with coordinates in the algebraic closure $\overline{\mathbb{Q}}$,
together with the point at infinity, and let $W[p]$ be its $p$-torsion subgroup, viewed as a
$\mathbb{Z}/p\mathbb{Z}$-module. Let $\rho$ be the mod-$p$ Galois representation of the absolute
Galois group $G_{\mathbb{Q}}$ of $\mathbb{Q}$ on $W[p]$. Its determinant character is the group
homomorphism $G_{\mathbb{Q}} \to (\mathbb{Z}/p\mathbb{Z})^\times$ sending $\sigma$ to the
determinant of the $\mathbb{Z}/p\mathbb{Z}$-linear automorphism $\rho(\sigma)$ of $W[p]$.

The determinant does not depend on a choice of basis, so no basis of $W[p]$ is fixed. The
definition is unconditional: if $W[p]$ has no finite basis over $\mathbb{Z}/p\mathbb{Z}$, the
character is constantly $1$. -/
noncomputable def galDetHom :
    Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ :=
  LinearEquiv.det.comp (galRep W p)

end MetaMathlibExt
