/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.GradedPairingTuple

/-!
# Tuple pairing formulas under cochain isomorphisms

Let P:K₁⊗K₂ → K₃ be a graded pairing of nonnegative cochain complexes
of abelian groups, and let a:K₁ ≅ L₁, b:K₂ ≅ L₂, c:K₃ ≅ L₃.
Choose tuple evaluations on the L-complexes, front and back tuple maps,
and a pairing of their value types. If evaluation of c(P(x⊗y)) agrees
with the value pairing of the evaluations of a(x) and b(y), then
Q=c ∘ P ∘ (a⁻¹⊗b⁻¹) satisfies the tuple evaluation formula on L₁,L₂,L₃.
All tuple and value types may have independent universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe s x y z t u v
open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- Let P:K₁⊗K₂ → K₃ be a graded pairing of nonnegative cochain complexes
of abelian groups and a:K₁ ≅ L₁, b:K₂ ≅ L₂, c:K₃ ≅ L₃ cochain
isomorphisms. Choose evaluations left_p:L₁ᵖ → T_p → X,
right_q:L₂ᑫ → U_q → Y, target_n:L₃ⁿ → V_n → Z, front and back
maps V_{p+q} → T_p,U_q, and pair:X → Y → Z.
Assume, for every p,q,x,y,v, that
target_{p+q}(c(P_{p,q}(x⊗₍ℤ₎y)))(v)
=pair(left_p(a(x))(front(v)),right_q(b(y))(back(v))).
Then the transported pairing Q=c ∘ P ∘ (a⁻¹⊗b⁻¹) satisfies the
tuple pairing formula for these evaluations. -/
theorem nativeGradedPairingTupleProperty_whisker
    {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex AddCommGrpCat.{s} ℕ}
    (P : HomologicalComplex.CochainGradedPairing K₁ K₂ K₃)
    (a : K₁ ≅ L₁) (b : K₂ ≅ L₂) (c : K₃ ≅ L₃)
    (T : ℕ → Type t) (U : ℕ → Type u) (V : ℕ → Type v)
    (X : Type x) (Y : Type y) (Z : Type z)
    (left : ∀ n, L₁.X n → T n → X) (right : ∀ n, L₂.X n → U n → Y)
    (target : ∀ n, L₃.X n → V n → Z)
    (front : ∀ p q, V (p + q) → T p) (back : ∀ p q, V (p + q) → U q)
    (pair : X → Y → Z)
    (h : ∀ p q (x : K₁.X p) (y : K₂.X q) (t : V (p + q)),
      target (p + q) ((c.hom.f (p + q)).hom ((P.pair p q).hom (x ⊗ₜ[ℤ] y))) t =
        pair (left p ((a.hom.f p).hom x) (front p q t))
          (right q ((b.hom.f q).hom y) (back p q t))) :
    nativeGradedPairingTupleProperty (P.whisker a.inv b.inv c.hom)
      T U V X Y Z left right target front back pair := by
  intro p q x y t
  change target (p + q) ((c.hom.f (p + q)).hom
      ((P.pair p q).hom ((a.inv.f p).hom x ⊗ₜ[ℤ] (b.inv.f q).hom y))) t = _
  have hx : (a.hom.f p).hom ((a.inv.f p).hom x) = x :=
    congrArg (fun f : L₁ ⟶ L₁ => (f.f p).hom x) a.inv_hom_id
  have hy : (b.hom.f q).hom ((b.inv.f q).hom y) = y :=
    congrArg (fun f : L₂ ⟶ L₂ => (f.f q).hom y) b.inv_hom_id
  have hp := h p q ((a.inv.f p).hom x) ((b.inv.f q).hom y) t
  rw [hx, hy] at hp
  exact hp

end CategoryTheory
