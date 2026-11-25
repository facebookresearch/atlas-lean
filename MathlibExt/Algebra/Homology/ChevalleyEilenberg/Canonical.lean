/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Exterior
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.BracketBoundaryRecursion
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Category
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.DerivationPure

/-!
# Canonical Chevalley–Eilenberg chain models

The exterior boundary constructed from the Lie bracket and Jacobi identity
has the ordered pair formula on every decomposable wedge. It defines a
canonical model over any commutative ring. Each bracket-presented model is
compared to it by the identity Lie algebra map, and Lie algebra homomorphisms
induce morphisms of canonical models.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The adjoint exterior action replaces each factor of a pure word by its
bracket with the acting vector. -/
theorem adjointAction_ιMulti (x : L) (n : ℕ) (v : Fin n → L) :
    adjointAction R L x (ExteriorAlgebra.ιMulti R n v) =
      ∑ i : Fin n, ExteriorAlgebra.ιMulti R n (Function.update v i ⁅x, v i⁆) :=
  ExteriorAlgebra.derivation_ιMulti R L (LieAlgebra.ad R L x) n v

/-- The canonical exterior boundary agrees with the ordered bracket sum
on every decomposable wedge. -/
theorem boundary_ιMulti (n : ℕ) (v : Fin (n + 1) → L) :
    boundary R L (ExteriorAlgebra.ιMulti R (n + 1) v) =
      (bracketBoundary R L n v : ExteriorAlgebra R L) := by
  induction n with
  | zero =>
      simp [ExteriorAlgebra.ιMulti_succ_apply, bracketBoundary]
  | succ n ih =>
      have hv : v = Matrix.vecCons (v 0) (Matrix.vecTail v) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hv, bracketBoundary_vecCons_update_coe R L n]
      rw [ExteriorAlgebra.ιMulti_succ_apply, Matrix.cons_val_zero, Matrix.tail_cons]
      rw [boundary_ι_mul, adjointAction_ιMulti, ih]

/-- The degree-restricted differential has the canonical pure-wedge
presentation, from the canonical exterior boundary. -/
theorem differential_apply_ιMulti (n : ℕ) (v : Fin (n + 1) → L) :
    differential R L n (exteriorPower.ιMulti R (n + 1) v) =
      bracketBoundary R L n v := by
  apply Subtype.ext
  simpa only [differential_coe, exteriorPower.ιMulti_apply_coe] using
    boundary_ιMulti R L n v

/-- Canonical CE data, with both the pure-wedge formula and square-zero
derived from the Lie algebra laws. -/
def canonicalPresentedData : PresentedData R L (bracketBoundary R L) where
  toChainData := canonicalChainData R L
  d_apply_ιMulti := differential_apply_ιMulti R L

/-- The canonical CE model attached to a Lie algebra over any commutative
ring. No freeness or chosen differential is needed. -/
def canonicalModel : Model.{u, v} R where
  carrier := L
  data := canonicalPresentedData R L

/-- The canonical comparison of any bracket-presented model with the
model constructed from its underlying Lie algebra. -/
def modelIsoCanonical (X : Model.{u, v} R) : X ≅ canonicalModel R X.carrier where
  hom := Model.Hom.ofLieHom X (canonicalModel R X.carrier) LieHom.id
  inv := Model.Hom.ofLieHom (canonicalModel R X.carrier) X LieHom.id
  hom_inv_id := by
    apply Model.Hom.ext
    rfl
  inv_hom_id := by
    apply Model.Hom.ext
    rfl

/-- A Lie algebra map induces a morphism of canonical CE models. -/
def canonicalMap
    {L' : Type v} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') :
    canonicalModel R L ⟶ canonicalModel R L' :=
  Model.Hom.ofLieHom (canonicalModel R L) (canonicalModel R L') f

@[simp]
theorem canonicalMap_id :
    canonicalMap R L (LieHom.id : L →ₗ⁅R⁆ L) = 𝟙 (canonicalModel R L) := by
  apply Model.Hom.ext
  rfl

@[simp]
theorem canonicalMap_comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    canonicalMap R L f ≫ canonicalMap R L' g = canonicalMap R L (g.comp f) := by
  apply Model.Hom.ext
  rfl

end ChevalleyEilenberg
