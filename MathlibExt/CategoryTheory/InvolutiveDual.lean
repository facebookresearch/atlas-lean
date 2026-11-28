/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/CategoryTheory/InvolutiveDual.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites

/-!
# Involutive contravariant endofunctors

A contravariant endofunctor `F : Cᵒᵖ ⥤ C` is *involutive* when double dualization is naturally
isomorphic to the identity by an isomorphism satisfying the triangle identity
`CategoryTheory.Functor.IsInvolutiveDual`. This constrains the chosen isomorphism, not just its
existence: rescaling the linear double-dual isomorphism by a nonzero scalar `c` with `c ^ 2 ≠ 1`
breaks it. The linear dual on finite-dimensional vector spaces and finite dualization of finite
locally free Hopf algebras are the motivating examples.

Turning such an `F` into an equivalence `Cᵒᵖ ≌ C` by `CategoryTheory.Functor.asEquivalence`
loses the involutivity: the inverse produced there is an abstract quasi-inverse, so no theorem
identifies it with `F` again. `CategoryTheory.Functor.dualityEquivalence` instead takes the
double-dual isomorphism as input and returns an equivalence whose inverse is `F.rightOp`, so
both directions and both structural isomorphisms compute.

## Main declarations

* `CategoryTheory.Functor.IsInvolutiveDual`: the triangle identity a double-dual isomorphism
  must satisfy.
* `CategoryTheory.Functor.dualityEquivalence`: the anti-equivalence attached to an involutive
  contravariant endofunctor, together with the computations of its functor, inverse, unit and
  counit in both directions.
-/

public section

namespace CategoryTheory

open Opposite

universe v u

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ C) (ev : 𝟭 C ≅ F.rightOp ⋙ F)

namespace Functor

/-- The triangle identity for a double-dual isomorphism `ev : 𝟭 C ≅ F.rightOp ⋙ F`: dualizing
`ev.inv` at `X` and then applying `ev.inv` at the dual of `X` is the identity. -/
abbrev IsInvolutiveDual : Prop :=
  ∀ X : C, F.map (ev.inv.app X).op ≫ ev.inv.app (F.obj (op X)) = 𝟙 (F.obj (op X))

variable (triangle : IsInvolutiveDual F ev)

/-- An involutive contravariant endofunctor is an anti-equivalence.

The inverse of the double-dual isomorphism `ev` plays the role of the counit, and the opposite
of that inverse plays the role of the unit, so unlike `CategoryTheory.Functor.asEquivalence` the
inverse of the resulting equivalence is `F.rightOp`: dualizing back is the same operation as
dualizing.

The body is exposed so that `functor` and `inverse` reduce to `F` and `F.rightOp` outside this
file: the unit and counit computations below only typecheck after that reduction. -/
@[expose, simps! functor inverse]
def dualityEquivalence : Cᵒᵖ ≌ C where
  functor := F
  inverse := F.rightOp
  -- `(𝟭 C).op` and `(F.rightOp ⋙ F).op` are `𝟭 Cᵒᵖ` and `F ⋙ F.rightOp` up to eta for
  -- `Opposite`, which is why `Functor.opId` is `Iso.refl`.
  unitIso := NatIso.op ev.symm
  counitIso := ev.symm
  functor_unitIso_comp X := triangle X.unop

/-- The unit of `dualityEquivalence` is the opposite of the inverse double-dual isomorphism. -/
@[simp]
theorem dualityEquivalence_unitIso_hom_app (X : Cᵒᵖ) :
    (dualityEquivalence F ev triangle).unitIso.hom.app X = (ev.inv.app X.unop).op :=
  (rfl)

/-- The counit of `dualityEquivalence` is the inverse double-dual isomorphism. -/
@[simp]
theorem dualityEquivalence_counitIso_hom_app (X : C) :
    (dualityEquivalence F ev triangle).counitIso.hom.app X = ev.inv.app X :=
  (rfl)

/-- The inverse unit of `dualityEquivalence` is the opposite of the double-dual isomorphism. -/
@[simp]
theorem dualityEquivalence_unitIso_inv_app (X : Cᵒᵖ) :
    (dualityEquivalence F ev triangle).unitIso.inv.app X = (ev.hom.app X.unop).op :=
  (rfl)

/-- The inverse counit of `dualityEquivalence` is the double-dual isomorphism. -/
@[simp]
theorem dualityEquivalence_counitIso_inv_app (X : C) :
    (dualityEquivalence F ev triangle).counitIso.inv.app X = ev.hom.app X :=
  (rfl)

end Functor

end CategoryTheory
