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

Frozen source: the arXiv source file `gonzalez-lozano_v11b_arxiv.tex`, SHA-256
`33306eccf5fce60cc116e22c4227a9125a35370982c51473be94db57ef21abc9`.

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

/-- An element of the absolute Galois group of `ℚ` viewed as an algebra
equivalence of the algebraic closure. `Field.absoluteGaloisGroup` is defined
as this type, so this is the identity bridge; it is stated explicitly because
bare coercion ascriptions are fragile in the action proofs below. -/
noncomputable def galAlgEquiv (σ : Field.absoluteGaloisGroup ℚ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

variable (W : Affine ℚ)

/-- The natural Galois action on affine nonsingular points of the base-changed
curve `W` over the algebraic closure of `ℚ`, via `Affine.Point.map`.
This is the pointwise form of the representation `ρ_{E,p}` of the source. -/
noncomputable def galPointHom (σ : Field.absoluteGaloisGroup ℚ) :
    Affine.Point (W.baseChange (AlgebraicClosure ℚ)) →+
      Affine.Point (W.baseChange (AlgebraicClosure ℚ)) :=
  Affine.Point.map (galAlgEquiv σ).toAlgHom

/-- The bridge preserves multiplication definitionally; recorded for rewriting
in the action proofs. -/
@[simp] theorem galAlgEquiv_mul (σ τ : Field.absoluteGaloisGroup ℚ) :
    galAlgEquiv (σ * τ) = galAlgEquiv σ * galAlgEquiv τ := rfl

/-- The bridge preserves inverses definitionally. -/
theorem galAlgEquiv_inv (σ : Field.absoluteGaloisGroup ℚ) :
    galAlgEquiv σ⁻¹ = (galAlgEquiv σ)⁻¹ := rfl

/-- The algebra-homomorphism form of the bridge is multiplicative. -/
theorem galToAlgHom_comp (σ τ : Field.absoluteGaloisGroup ℚ) :
    (galAlgEquiv (σ * τ)).toAlgHom =
      (galAlgEquiv σ).toAlgHom.comp (galAlgEquiv τ).toAlgHom := by
  ext x
  change (galAlgEquiv (σ * τ)) x = _
  rw [galAlgEquiv_mul, AlgEquiv.mul_apply]
  rfl

/-- The identity automorphism acts trivially on points. -/
theorem galPointHom_apply_one (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
    galPointHom W 1 P = P := by
  cases P <;> rfl

/-- The point action is multiplicative. -/
theorem galPointHom_apply_mul (σ τ : Field.absoluteGaloisGroup ℚ)
    (P : Affine.Point (W.baseChange (AlgebraicClosure ℚ))) :
    galPointHom W (σ * τ) P = galPointHom W σ (galPointHom W τ P) := by
  change Affine.Point.map _ P = Affine.Point.map _ (Affine.Point.map _ P)
  rw [galToAlgHom_comp, ← Affine.Point.map_map]

variable (p : ℕ)

/-- The `p`-torsion subgroup of the base-changed affine point group; this is
the source's `E[p]`. -/
noncomputable def torsionPts :=
  AddSubgroup.torsionBy (Affine.Point (W.baseChange (AlgebraicClosure ℚ))) (p : ℤ)

/-- The `ZMod p`-module structure on `p`-torsion points. -/
noncomputable instance instZModModule : Module (ZMod p) (torsionPts W p) :=
  AddSubgroup.torsionBy.zmodModule

/-- Membership in `torsionPts` is the `p`-torsion condition. -/
theorem mem_torsionPts_iff {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))} :
    x ∈ torsionPts W p ↔ p • x = 0 := by
  change x ∈ AddSubgroup.torsionBy _ _ ↔ _
  exact AddSubgroup.torsionBy.nsmul_iff

/-- The Galois point action preserves `p`-torsion. -/
theorem galPointHom_mem (σ : Field.absoluteGaloisGroup ℚ)
    {x : Affine.Point (W.baseChange (AlgebraicClosure ℚ))}
    (hx : x ∈ torsionPts W p) : galPointHom W σ x ∈ torsionPts W p := by
  rw [mem_torsionPts_iff] at hx ⊢
  rw [← map_nsmul]
  rw [hx, map_zero]

/-- The Galois action restricted to the `p`-torsion subtype. The ambient point
group is not a `ZMod p`-module, so restriction to the subtype comes first. -/
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

/-- The restricted action as a `ZMod p`-linear map. -/
noncomputable def galLinearMap (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p →ₗ[ZMod p] torsionPts W p :=
  (galTorsionHom W p σ).toZModLinearMap p

/-- The linear map acts pointwise as the point action. -/
theorem galLinearMap_apply (σ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p σ x = ⟨galPointHom W σ x.val, galPointHom_mem W p σ x.property⟩ :=
  rfl

/-- The identity acts as the identity linear map. -/
theorem galLinearMap_one_apply (x : torsionPts W p) :
    galLinearMap W p 1 x = x := by
  apply Subtype.ext
  change galPointHom W 1 x.val = x.val
  exact galPointHom_apply_one W x.val

/-- The linear action is multiplicative. -/
theorem galLinearMap_mul_apply (σ τ : Field.absoluteGaloisGroup ℚ)
    (x : torsionPts W p) :
    galLinearMap W p (σ * τ) x = galLinearMap W p σ (galLinearMap W p τ x) := by
  apply Subtype.ext
  change galPointHom W (σ * τ) x.val = galPointHom W σ (galPointHom W τ x.val)
  exact galPointHom_apply_mul W σ τ x.val

/-- Each Galois automorphism acts bijectively, with the inverse automorphism
supplying a two-sided inverse. -/
theorem galLinearMap_bijective (σ : Field.absoluteGaloisGroup ℚ) :
    Function.Bijective (galLinearMap W p σ) := by
  have hleft : Function.LeftInverse (galLinearMap W p σ⁻¹) (galLinearMap W p σ) := by
    intro x
    rw [← galLinearMap_mul_apply, inv_mul_cancel, galLinearMap_one_apply]
  have hright : Function.RightInverse (galLinearMap W p σ⁻¹) (galLinearMap W p σ) := by
    intro x
    rw [← galLinearMap_mul_apply, mul_inv_cancel, galLinearMap_one_apply]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The invertible `ZMod p`-linear action of a Galois automorphism on `E[p]`,
packaged via `LinearEquiv.ofBijective` to avoid normalizing
`toZModLinearMap` projections inside a manual `LinearEquiv` construction. -/
noncomputable def galLinearEquiv (σ : Field.absoluteGaloisGroup ℚ) :
    torsionPts W p ≃ₗ[ZMod p] torsionPts W p :=
  LinearEquiv.ofBijective _ (galLinearMap_bijective W p σ)

/-- The mod-`p` Galois representation `ρ_{E,p}` as a monoid homomorphism into
linear equivalences. -/
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

/-- The determinant of the mod-`p` representation, as a character with values
in `(ZMod p)ˣ`. `LinearEquiv.det` is basis independent (Mathlib proves
`detAux` does not depend on the basis), so no basis of `E[p]` is fixed.
It is defined unconditionally: on a module with no finite basis it takes the
value `1`. -/
noncomputable def galDetHom :
    Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ :=
  LinearEquiv.det.comp (galRep W p)

end MetaMathlibExt
