/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Exact

/-! Tests for subobjects, quotients, direct sums, exactness and faithfulness of admissible
representations: the inclusion of a subrepresentation and the projection onto the quotient as
intertwining maps, left exactness of `D_S` for every ring, `D_S` of a product, and for a regular
ring the closure of admissible representations under subobjects, quotients and direct sums and
the exactness and faithfulness of `D_S`, in particular for the trivial representation and for a
field with any action. -/

open scoped TensorProduct

open Representation

variable {F G S V W U : Type*} [Field F] [Group G] [CommRing S] [Algebra F S]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

-- The inclusion and the projection of a subrepresentation form a short exact sequence.
example {ρ : Representation F G V} (W' : Subrepresentation ρ) (w : W'.toSubmodule) :
    W'.subtype w = w :=
  Subrepresentation.subtype_apply W' w

example {ρ : Representation F G V} (W' : Subrepresentation ρ) :
    Function.Injective W'.subtype ∧ Function.Surjective W'.mkQ ∧
      Function.Exact W'.subtype W'.mkQ :=
  ⟨W'.subtype_injective, W'.mkQ_surjective, W'.exact_subtype_mkQ⟩

-- `D_S` is left exact for every ring `S` and every family `act`.
example {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (act : G → S →ₐ[F] S) (H : Subgroup G) {f : ρ.IntertwiningMap σ}
    {g : σ.IntertwiningMap τ} (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (periodsMap act H f) ∧
      Function.Exact (periodsMap act H f) (periodsMap act H g) :=
  ⟨periodsMap_injective hf, exact_periodsMap_of_injective hf hfg⟩

-- `D_S(V × W) ≃ D_S(V) × D_S(W)`, by the projections.
example (ρ : Representation F G V) (σ : Representation F G W) (act : G → S →ₐ[F] S)
    (H : Subgroup G) (x : (ρ.prod σ).periods act H) :
    ((periodsProdEquiv ρ σ act H x).1 : S ⊗[F] V) =
      (IntertwiningMap.fst F ρ σ).toLinearMap.baseChange S x := by
  simp

section Regular

variable [IsDomain S] {act : G →* (S →ₐ[F] S)} {H : Subgroup G}

-- For a regular ring, subrepresentations and quotients of admissible representations are
-- admissible, and so are the terms of a short exact sequence with admissible middle term.
example (hS : IsRegularPeriodRing act H) {ρ : Representation F G V}
    (h : ρ.IsAdmissible act H) (W' : Subrepresentation ρ) :
    W'.toRepresentation.IsAdmissible act H ∧ W'.quotient.IsAdmissible act H :=
  ⟨hS.isAdmissible_toRepresentation h W', hS.isAdmissible_quotient h W'⟩

example (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} {σ : Representation F G W}
    {τ : Representation F G U} {f : σ.IntertwiningMap ρ} {g : ρ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h : ρ.IsAdmissible act H) :
    σ.IsAdmissible act H ∧ τ.IsAdmissible act H :=
  hS.isAdmissible_of_exact hf hg hfg h

-- `D_S` maps a short exact sequence with admissible middle term to a short exact sequence.
example (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} {σ : Representation F G W}
    {τ : Representation F G U} {f : σ.IntertwiningMap ρ} {g : ρ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h : ρ.IsAdmissible act H) :
    Function.Injective (periodsMap act H f) ∧
      Function.Exact (periodsMap act H f) (periodsMap act H g) ∧
      Function.Surjective (periodsMap act H g) :=
  hS.shortExact_periodsMap hf hg hfg h

-- Exactness at the middle needs only the first term to be admissible.
example (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} {σ : Representation F G W}
    {τ : Representation F G U} {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hfg : Function.Exact f g) (h : ρ.IsAdmissible act H) :
    Function.Exact (periodsMap act H f) (periodsMap act H g) :=
  hS.exact_periodsMap hfg h

-- Direct sums.
example (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} {σ : Representation F G W} :
    (ρ.prod σ).IsAdmissible act H ↔ ρ.IsAdmissible act H ∧ σ.IsAdmissible act H :=
  hS.isAdmissible_prod_iff

-- Faithfulness: intertwining maps out of an admissible representation are determined by `D_S`.
example (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} {σ : Representation F G W}
    (h : ρ.IsAdmissible act H) {f f' : ρ.IntertwiningMap σ}
    (hff' : periodsMap act H f = periodsMap act H f') : f = f' :=
  hS.eq_of_periodsMap_eq h hff'

-- The trivial representation is admissible, so its subrepresentations, quotients and direct
-- sums with itself are admissible.
example (hS : IsRegularPeriodRing act H) [FiniteDimensional F V]
    (W' : Subrepresentation (trivial F G V)) :
    W'.quotient.IsAdmissible act H ∧
      ((trivial F G V).prod (trivial F G V)).IsAdmissible act H := by
  have h : (trivial F G V).IsAdmissible act H := HasFixedBasis.isAdmissible
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩
  exact ⟨hS.isAdmissible_quotient h W', hS.isAdmissible_prod_iff.2 ⟨h, h⟩⟩

end Regular

-- For a field with any action, `D_S` is faithful on admissible representations.
example {L : Type*} [Field L] [Algebra F L] (act : G →* (L →ₐ[F] L)) (H : Subgroup G)
    {ρ : Representation F G V} {σ : Representation F G W} (h : ρ.IsAdmissible act H)
    {f f' : ρ.IntertwiningMap σ} (hff' : periodsMap act H f = periodsMap act H f') : f = f' :=
  (isRegularPeriodRing_of_isField (Field.toIsField L) act H).eq_of_periodsMap_eq h hff'
