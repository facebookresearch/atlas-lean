/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Collapsing a simplicial subcomplex

For `A : X.Subcomplex`, the pointed quotient `X/A` is the pushout of the
inclusion `A.ι : A ⟶ X` along the unique map `A ⟶ Δ[0]`. This file exposes
the two pushout legs, the collapsed vertex, direct descent from the pushout
universal property, and finiteness of the quotient when `X` is finite.

Here `SSet.stdSimplex` denotes the representable simplicial standard simplex;
it is unrelated to the topological type `Convexity.StdSimplex`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial
open scoped Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The pointed quotient obtained by collapsing `A` inside `X`. -/
noncomputable def quotient : SSet.{u} :=
  pushout A.ι (stdSimplex.isTerminalObj₀.from A)

/-- The canonical morphism from `X` to `X/A`. -/
noncomputable def toQuotient : X ⟶ A.quotient :=
  pushout.inl A.ι (stdSimplex.isTerminalObj₀.from A)

/-- The point leg `Δ[0] ⟶ X/A` of the defining pushout. -/
noncomputable def pointToQuotient : Δ[0] ⟶ A.quotient :=
  pushout.inr A.ι (stdSimplex.isTerminalObj₀.from A)

/-- The canonical square defining `X/A`. -/
lemma quotient_isPushout :
    IsPushout A.ι (stdSimplex.isTerminalObj₀.from A)
      A.toQuotient A.pointToQuotient :=
  IsPushout.of_hasPushout _ _

/-- The vertex of `X/A` to which `A` is collapsed. -/
noncomputable def quotient₀ : A.quotient _⦋0⦌ :=
  yonedaEquiv A.pointToQuotient

@[simp]
lemma yonedaEquiv_symm_quotient₀ :
    yonedaEquiv.symm A.quotient₀ = A.pointToQuotient :=
  Equiv.symm_apply_apply _ _

@[simp]
lemma pointToQuotient_eq_const :
    A.pointToQuotient = const A.quotient₀ := by
  rw [← yonedaEquiv_symm_zero A.quotient₀, yonedaEquiv_symm_quotient₀]

/-- The inclusion of `A` followed by the quotient map is constant at the
collapsed vertex. -/
@[reassoc (attr := simp)]
lemma ι_quotient : A.ι ≫ A.toQuotient = const A.quotient₀ := by
  calc
    A.ι ≫ A.toQuotient =
        stdSimplex.isTerminalObj₀.from A ≫ A.pointToQuotient :=
      A.quotient_isPushout.w
    _ = stdSimplex.isTerminalObj₀.from A ≫ const A.quotient₀ := by
      rw [pointToQuotient_eq_const]
    _ = const A.quotient₀ := comp_const _ _

section Descent

variable {T : SSet.{u}} (f : X ⟶ T) (t₀ : T _⦋0⦌)

/-- Descend a map `X ⟶ T` which is constant on `A`. -/
noncomputable def descQuotient (hf : A.ι ≫ f = const t₀) : A.quotient ⟶ T :=
  A.quotient_isPushout.desc f (const t₀) (by simpa using hf)

/-- Direct computation of a descended map on the `X` leg. -/
@[reassoc (attr := simp)]
lemma toQuotient_descQuotient (hf : A.ι ≫ f = const t₀) :
    A.toQuotient ≫ A.descQuotient f t₀ hf = f := by
  simp [descQuotient]

/-- Direct computation of a descended map at the collapsed vertex. -/
@[simp]
lemma descQuotient_app_quotient₀ (hf : A.ι ≫ f = const t₀) :
    (A.descQuotient f t₀ hf).app _ A.quotient₀ = t₀ := by
  apply yonedaEquiv.symm.injective
  calc
    yonedaEquiv.symm ((A.descQuotient f t₀ hf).app _ A.quotient₀) =
        A.pointToQuotient ≫ A.descQuotient f t₀ hf := by
      rw [← yonedaEquiv_symm_quotient₀]
      exact (yonedaEquiv_symm_comp _ _).symm
    _ = const t₀ := by simp [descQuotient]
    _ = yonedaEquiv.symm t₀ := by rw [yonedaEquiv_symm_zero]

end Descent

/-- Two maps from `X/A` agree when they agree on `X` and at the collapsed
vertex. -/
@[ext]
lemma quotient_hom_ext {T : SSet.{u}} {f g : A.quotient ⟶ T}
    (hX : A.toQuotient ≫ f = A.toQuotient ≫ g)
    (hpt : f.app _ A.quotient₀ = g.app _ A.quotient₀) : f = g := by
  apply A.quotient_isPushout.hom_ext hX
  have h := congrArg yonedaEquiv.symm hpt
  calc
    A.pointToQuotient ≫ f = yonedaEquiv.symm A.quotient₀ ≫ f := by
      rw [yonedaEquiv_symm_quotient₀]
    _ = yonedaEquiv.symm (f.app _ A.quotient₀) := yonedaEquiv_symm_comp _ _
    _ = yonedaEquiv.symm (g.app _ A.quotient₀) := h
    _ = yonedaEquiv.symm A.quotient₀ ≫ g := (yonedaEquiv_symm_comp _ _).symm
    _ = A.pointToQuotient ≫ g := by rw [yonedaEquiv_symm_quotient₀]

/-- A morphism whose image lies in `A` becomes constant after passage to
`X/A`. -/
@[reassoc]
lemma comp_toQuotient_eq_const {Y : SSet.{u}} (f : Y ⟶ X)
    (hf : A.preimage f = ⊤) :
    f ≫ A.toQuotient = const A.quotient₀ := by
  let liftToA : Y ⟶ A := A.lift f ((A.preimage_eq_top_iff f).mp hf)
  calc
    f ≫ A.toQuotient = (liftToA ≫ A.ι) ≫ A.toQuotient := by
      rw [A.lift_ι]
    _ = liftToA ≫ (A.ι ≫ A.toQuotient) := Category.assoc _ _ _
    _ = liftToA ≫ const A.quotient₀ := by rw [ι_quotient]
    _ = const A.quotient₀ := comp_const _ _

instance [X.Finite] : A.quotient.Finite := by
  apply finite_of_isColimit A.quotient_isPushout.isColimit
  rintro (⟨⟩ | ⟨⟨⟩⟩) <;> dsimp <;> infer_instance

end SSet.Subcomplex
