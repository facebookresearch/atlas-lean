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

/-! # Original tuple pairing compatibility through actual complex isomorphisms -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe s x y z t u v
open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine tuple compatibility of the original pairing and three actual
complex maps determines the tuple law of the actual whiskered pairing. -/
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
