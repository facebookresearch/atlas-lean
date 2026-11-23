/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/LinearAlgebra/Graded/LinearMap.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Homogeneous linear maps

This file records the degree of a linear map between modules equipped with families of graded
subobjects. A linear map has degree `q` when it maps everything in the degree-`p` piece of the
source into the degree-`p + q` piece of the target. This is a containment condition, so no
direct-sum hypothesis is imposed and a map can be homogeneous of several degrees at once. The
families are indexed by an arbitrary `SetLike` type, so the homogeneity predicate and the additive
closure lemmas cover gradings by submodules, additive subgroups and additive submonoids alike.
`LinearMap.IsHomogeneous.smul` additionally needs the target pieces to be closed under a
distributive scalar action, and `LinearMap.homogeneousSubmodule` needs them to be additive
submonoids closed under a module action, i.e. a submodule-valued grading.

The multilinear counterpart, and the degree calculus for substitution, are in
`TauCeti.LinearAlgebra.Graded.Multilinear`.

## Main definitions

* `LinearMap.IsHomogeneous`: a linear map shifts homogeneous degree by a fixed amount.
* `LinearMap.homogeneousSubmodule`: the submodule of linear maps of a fixed degree.

## Main results

* `LinearMap.IsHomogeneous.comp`: degrees add under composition of linear maps.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uι uM uN uP

namespace LinearMap

section Semiring

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- A linear map is homogeneous of degree `q` if it maps the degree-`p` piece of `𝒜` into the
degree-`p + q` piece of `ℬ`. No direct-sum hypothesis on the families is needed. -/
def IsHomogeneous (f : M →ₗ[R] N) (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) : Prop :=
  ∀ ⦃p : ι⦄ ⦃x : M⦄, x ∈ 𝒜 p → f x ∈ ℬ (p + q)

/-- Homogeneity of degree `q` is exactly the mapping condition on homogeneous elements. This is a
convenient introduction rule, and `IsHomogeneous.map_mem` is the corresponding elimination rule. -/
theorem isHomogeneous_def {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} :
    IsHomogeneous f 𝒜 ℬ q ↔ ∀ (p : ι) (x : M), x ∈ 𝒜 p → f x ∈ ℬ (p + q) :=
  ⟨fun hf _ _ hx ↦ hf hx, fun hf _ _ hx ↦ hf _ _ hx⟩

/-- Apply a homogeneous linear map to a homogeneous element. -/
theorem IsHomogeneous.map_mem {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q p : ι} (hf : IsHomogeneous f 𝒜 ℬ q) {x : M} (hx : x ∈ 𝒜 p) :
    f x ∈ ℬ (p + q) :=
  hf hx

/-- The zero linear map is homogeneous of every degree. -/
@[simp]
theorem isHomogeneous_zero [ZeroMemClass σN N] (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) :
    IsHomogeneous (0 : M →ₗ[R] N) 𝒜 ℬ q := by
  intro p x _
  simp

/-- A sum of linear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.add [AddMemClass σN N] {f g : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f + g) 𝒜 ℬ q := by
  intro p x hx
  simpa using add_mem (hf hx) (hg hx)

/-- The identity linear map is homogeneous of degree zero. -/
@[simp]
theorem isHomogeneous_id (𝒜 : ι → σM) :
    IsHomogeneous (LinearMap.id : M →ₗ[R] M) 𝒜 𝒜 0 := by
  intro p x hx
  simpa using hx

/-- Degrees add under composition of linear maps. -/
@[grind →]
theorem IsHomogeneous.comp {P : Type uP} {σP : Type*} [AddCommMonoid P] [Module R P]
    [SetLike σP P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} {𝒜 : ι → σM}
    {ℬ : ι → σN} {𝒞 : ι → σP} {q r : ι}
    (hg : IsHomogeneous g ℬ 𝒞 r) (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (g.comp f) 𝒜 𝒞 (q + r) := by
  intro p x hx
  simpa only [_root_.LinearMap.comp_apply, add_assoc] using hg (hf hx)

end Semiring

section Neg

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommGroup N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- The negative of a homogeneous linear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.neg [NegMemClass σN N] {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (-f) 𝒜 ℬ q := by
  intro p x hx
  simpa using neg_mem (hf hx)

/-- A difference of linear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.sub [AddMemClass σN N] [NegMemClass σN N] {f g : M →ₗ[R] N}
    {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q)
    (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f - g) 𝒜 ℬ q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Neg

section Scalars

variable {R : Type uR} {S : Type*} {ι : Type uι} {M : Type uM} {N : Type uN}
  {σM : Type*} {σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- A scalar multiple of a homogeneous linear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.smul [DistribSMul S N] [SMulCommClass R S N]
    [SMulMemClass σN S N] {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (s : S) :
    IsHomogeneous (s • f) 𝒜 ℬ q := by
  intro p x hx
  simpa using SMulMemClass.smul_mem s (hf hx)

/-- Linear maps of a fixed degree form a submodule over any scalar ring acting on the target. -/
def homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N] (𝒜 : ι → σM)
    (ℬ : ι → σN) (q : ι) : Submodule S (M →ₗ[R] N) where
  carrier := {f | IsHomogeneous f 𝒜 ℬ q}
  zero_mem' := isHomogeneous_zero 𝒜 ℬ q
  add_mem' hf hg := hf.add hg
  smul_mem' s _ hf := hf.smul s

@[simp, grind =]
theorem mem_homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N]
    {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} :
    f ∈ homogeneousSubmodule (S := S) 𝒜 ℬ q ↔ IsHomogeneous f 𝒜 ℬ q :=
  Iff.rfl

end Scalars

section Reindex

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddCommMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Translating the indices of both gradings by the same amount preserves homogeneity. -/
theorem IsHomogeneous.reindex {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (p : ι) :
    IsHomogeneous f (fun n ↦ 𝒜 (n + p)) (fun n ↦ ℬ (n + p)) q := fun n _ hx ↦ by
  have h := hf.map_mem hx
  rwa [add_right_comm] at h

end Reindex

end LinearMap

end TauCeti
