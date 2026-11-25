/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_ConjQuotSubfunctor.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import MathlibExt.RingTheory.Deformations.TraceAlgebra

/-!
# Images of lifting conditions in strict equivalence classes

A *lifting condition* is a subfunctor `F` of the representation functor `repnFunctor n G 𝓞`. Its
image under the quotient map to strict equivalence classes is a subfunctor
`conjQuotSubfunctor n F` of `repnQuotFunctor n G 𝓞`, and `F` surjects onto it. We also record
two properties of lifting conditions: stability under strict equivalence (`ConjStable`) and being
reflected by injective morphisms of coefficient algebras (`ReflectedByInjective`).

## Main definitions

* `Deformation.conjQuotSubfunctor n F`: the image of `F` in strict equivalence classes.
* `Deformation.condLiftToDeformation n F`: the surjection `F ⟶ conjQuotSubfunctor n F`.
* `Deformation.ConjStable n F`, `Deformation.ReflectedByInjective n F`.
-/

@[expose] public section

universe u v w

open CategoryTheory Function IsLocalRing

namespace Deformation

section ConjQuot

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {G : Type w} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

open ProartinianCat

variable (n) in
/-- The image of a subfunctor of the representation functor in the functor of strict
equivalence classes. -/
noncomputable def conjQuotSubfunctor (F : Subfunctor (repnFunctor n G 𝓞)) :
    Subfunctor (repnQuotFunctor n G 𝓞) where
  obj R := (toRepnQuot n G 𝓞).app R '' F.obj R
  map {R S} f := by
    rintro _ ⟨ρ', hρ', rfl⟩
    exact ⟨(repnFunctor n G 𝓞).map f ρ', F.map f hρ', rfl⟩

variable (n) in
theorem mem_conjQuotSubfunctor_obj_iff {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} (q : (repnQuotFunctor n G 𝓞).obj R) :
    q ∈ (conjQuotSubfunctor n F).obj R ↔
      ∃ ρ' ∈ F.obj R, (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) = q := by
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ', hρ', rfl⟩
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ', hρ', rfl⟩

variable (n) in
theorem mk_mem_conjQuotSubfunctor_obj {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} {ρ' : G →ₜ* GL n R} (hρ' : ρ' ∈ F.obj R) :
    (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) ∈ (conjQuotSubfunctor n F).obj R :=
  ⟨ρ', hρ', rfl⟩

variable (n) in
theorem conjQuotSubfunctor_mono {F F' : Subfunctor (repnFunctor n G 𝓞)} (h : F ≤ F') :
    conjQuotSubfunctor n F ≤ conjQuotSubfunctor n F' := by
  rintro R _ ⟨ρ', hρ', rfl⟩
  exact ⟨ρ', h _ hρ', rfl⟩

variable (n) in
/-- The natural map from a subfunctor of representations onto its image in strict
equivalence classes. -/
noncomputable def condLiftToDeformation (F : Subfunctor (repnFunctor n G 𝓞)) :
    F.toFunctor ⟶ (conjQuotSubfunctor n F).toFunctor where
  app R := TypeCat.ofHom
    fun ρ' => ⟨Quotient.mk'' ρ'.1, mk_mem_conjQuotSubfunctor_obj n ρ'.2⟩
  naturality R S f := by
    ext ρ'
    rfl

variable (n) in
theorem condLiftToDeformation_surjective (F : Subfunctor (repnFunctor n G 𝓞))
    (R : ProartinianCat 𝓞) :
    Function.Surjective ((condLiftToDeformation n F).app R) := by
  rintro ⟨q, hq⟩
  obtain ⟨ρ', hρ', hq'⟩ := (mem_conjQuotSubfunctor_obj_iff n q).mp hq
  exact ⟨⟨ρ', hρ'⟩, Subtype.ext hq'⟩

end ConjQuot

section Assembly

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {G : Type w} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

open ProartinianCat

variable (n) in
/-- A subfunctor of representations is *conjugation stable* if it is stable under strict
equivalence. -/
def ConjStable (F : Subfunctor (repnFunctor n G 𝓞)) : Prop :=
  ∀ {A : ProartinianCat 𝓞} {ρ' : G →ₜ* GL n A}, ρ' ∈ F.obj A →
    ∀ {γ : ConjAct (GL n A)}, γ ∈ conjKer (n := n) A → γ • ρ' ∈ F.obj A

variable (n) in
/-- A subfunctor of representations is *reflected by injections* if a representation whose
pushforward along an injective morphism lies in the subfunctor itself lies in it. -/
def ReflectedByInjective (F : Subfunctor (repnFunctor n G 𝓞)) : Prop :=
  ∀ {T A : ProartinianCat 𝓞} (ι : T ⟶ A), Function.Injective ι.hom →
    ∀ {σ : G →ₜ* GL n T}, (repnFunctor n G 𝓞).map ι σ ∈ F.obj A → σ ∈ F.obj T

end Assembly

end Deformation
