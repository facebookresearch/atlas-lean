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
# Canonical exterior Chevalley–Eilenberg models

Let R be a commutative ring and L an R-Lie algebra. The exterior
boundary defined by the bracket and Jacobi identity is square zero.
On a decomposable wedge its value is
d(x_0∧⋯∧x_n)=∑_{i<j}(−1)^{i+j}[x_i,x_j]∧x with i,j deleted,
with the bracket first and the remaining entries in their given order.
The degree-one boundary is zero and the degree-two boundary is −[x,y].

These differential objects give the canonical bracket-presented model
of L. Every other model with that same bracket prescription is
isomorphic to it through the identity Lie map. Lie homomorphisms
induce morphisms of the canonical models, over arbitrary R and
independent scalar and Lie-carrier universes.

Reference: C. Chevalley and S. Eilenberg, Cohomology theory of Lie groups
and Lie algebras (1948).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Let R be a commutative ring and L a Lie algebra over R.
Write E=ExteriorAlgebra_R(L), ι:L→E for its generator map,
and β_n for the bracket boundary on ordered (n+1)-tuples.
The adjoint exterior derivation satisfies
ad_x(v_0∧⋯∧v_{n-1})=∑_j v_0∧⋯∧[x,v_j]∧⋯∧v_{n-1}.
Each bracket replaces its factor in place. -/
theorem adjointAction_ιMulti (x : L) (n : ℕ) (v : Fin n → L) :
    adjointAction R L x (ExteriorAlgebra.ιMulti R n v) =
      ∑ i : Fin n, ExteriorAlgebra.ιMulti R n (Function.update v i ⁅x, v i⁆) :=
  ExteriorAlgebra.derivation_ιMulti R L (LieAlgebra.ad R L x) n v

/-- Let R be a commutative ring and L a Lie algebra over R.
Write E=ExteriorAlgebra_R(L), ι:L→E for its generator map,
and β_n for the bracket boundary on ordered (n+1)-tuples.
The exterior boundary on ιMulti(v), for v:Fin(n+1)→L,
is the image of β_n(v) in E. It is the ordered pair sum with
coefficient (−1)^{i+j} and bracket placed first. -/
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

/-- Let R be a commutative ring and L a Lie algebra over R.
Write E=ExteriorAlgebra_R(L), ι:L→E for its generator map,
and β_n for the bracket boundary on ordered (n+1)-tuples.
The restricted differential Λ_R^{n+1}L→Λ_R^nL sends
v_0∧⋯∧v_n to β_n(v), with the fixed ordered-pair signs. -/
theorem differential_apply_ιMulti (n : ℕ) (v : Fin (n + 1) → L) :
    differential R L n (exteriorPower.ιMulti R (n + 1) v) =
      bracketBoundary R L n v := by
  apply Subtype.ext
  simpa only [differential_coe, exteriorPower.ιMulti_apply_coe] using
    boundary_ιMulti R L n v

/-- Let R be a commutative ring and L a Lie algebra over R.
Write E=ExteriorAlgebra_R(L), ι:L→E for its generator map,
and β_n for the bracket boundary on ordered (n+1)-tuples.
The canonical square-zero differential together with its wedge
value β_n(v) gives PresentedData for the bracket prescription. -/
def canonicalPresentedData : PresentedData R L (bracketBoundary R L) where
  toChainData := canonicalChainData R L
  d_apply_ιMulti := differential_apply_ιMulti R L

/-- Let R be a commutative ring and L a Lie algebra over R.
Write E=ExteriorAlgebra_R(L), ι:L→E for its generator map,
and β_n for the bracket boundary on ordered (n+1)-tuples.
The Lie algebra L with its canonical bracket-presented exterior
differentials defines an object of the category of CE models. -/
def canonicalModel : Model.{u, v} R where
  carrier := L
  data := canonicalPresentedData R L

/-- Let R be commutative and X a model with an R-Lie carrier and
square-zero exterior differential presented by the canonical bracket
formula. X is isomorphic to the canonical model of its carrier,
with both model maps induced by the identity Lie homomorphism. -/
def modelIsoCanonical (X : Model.{u, v} R) : X ≅ canonicalModel R X.carrier where
  hom := Model.Hom.ofLieHom X (canonicalModel R X.carrier) LieHom.id
  inv := Model.Hom.ofLieHom (canonicalModel R X.carrier) X LieHom.id
  hom_inv_id := by
    apply Model.Hom.ext
    rfl
  inv_hom_id := by
    apply Model.Hom.ext
    rfl

/-- Let R be a commutative ring and L a Lie algebra over R.
Write E=ExteriorAlgebra_R(L), ι:L→E for its generator map,
and β_n for the bracket boundary on ordered (n+1)-tuples.
For an R-Lie homomorphism f:L→L′ in the same carrier universe,
the exterior maps Λ_R^n f define a morphism between the canonical
models of L and L′. -/
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
