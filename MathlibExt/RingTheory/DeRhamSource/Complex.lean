/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

/-
Portions of this file are adapted from:

`StacksFrontier/RingTheory/DeRham/Complex.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: module paths and outer namespace are adapted for Atlas; source-only documentation
cross-reference attributes are omitted. All original mathematical proof bodies are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import MathlibExt.RingTheory.DeRhamSource.Connection

namespace MathlibExt.DeRhamSource

open _root_.Algebra _root_.KaehlerDifferential

/-!
# The de Rham complex of a ring map, as a cochain complex

Let `A → B` be a map of commutative rings, let `Ω[B⁄A]` be the module of Kähler differentials
with its universal `A`-derivation `d = KaehlerDifferential.D A B`, and write
`Ω^p_{B/A} = ⋀[B]^p Ω[B⁄A]`.  `KaehlerDifferential.deRhamDifferential p` is the unique `A`-linear
map `Ω^p_{B/A} → Ω^{p+1}_{B/A}` with

`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`.

The property that makes that family a *complex*, that consecutive differentials compose to zero,
is `KaehlerDifferential.deRhamDifferential_comp_deRhamDifferential` of
`StacksFrontier/RingTheory/DeRham/Basic.lean`.  Here the family is packaged as an honest
`CochainComplex` of `A`-modules indexed by `ℕ`, together with the statement that the defining rule
above determines that complex.

## Main definitions

* `KaehlerDifferential.deRhamComplex`: **the de Rham complex `Ω^0_{B/A} → Ω^1_{B/A} → ⋯` of
  `B` over `A`** ([Stacks, Tag 0FKF]), as a `CochainComplex (ModuleCat A) ℕ`.  The construction
  takes no hypothesis: its arrows are `deRhamDifferential` and its square-zero condition is the
  theorem cited above.

## Main results

* `KaehlerDifferential.deRhamComplex_X` and `KaehlerDifferential.deRhamComplex_d`: the terms
  and the arrows of `deRhamComplex`.
* `KaehlerDifferential.deRhamComplex_d_smul_ιMulti_D`: the defining rule, read on the arrows of
  `deRhamComplex`.
* `KaehlerDifferential.deRhamComplex_unique`: any family of `A`-linear maps obeying the defining
  rule assembles into `deRhamComplex`, whatever square-zero proof it is given.

## Implementation notes

The terms are `A`-modules and not `B`-modules, because the differentials are `A`-linear only:
already in degree `0` the Leibniz rule gives `d (b b') = b · d b' + b' · d b`.  Unlike
`Stacks.DeRham.DifferentialDescent.SrcA`, which carries the `A`-module structure through the
`RestrictScalars` type synonym, the terms here are the exterior powers themselves with the
`A`-action they already have by `IsScalarTower A B _`; that is the structure
`deRhamDifferential` is stated for, so no transport along a synonym is ever needed.  Both ring
universes are tied together, `A B : Type u`, because the objects of `ModuleCat.{u} A` are types
in `Type u` while `⋀[B]^p Ω[B⁄A]` lives in `Type (max u v)`; this is forced by the target
category and not a choice.

## References

* [Stacks 0FKF](https://stacks.math.columbia.edu/tag/0FKF), the de Rham complex
* [Stacks 0FKG](https://stacks.math.columbia.edu/tag/0FKG), formula (26): the differentials
-/

open CategoryTheory

namespace KaehlerDifferential

universe u

section Complex

/-! From here the two ring universes are tied together, `A B : Type u`.  That is forced by
`ModuleCat.{u}` being the target category of the complex, not chosen. -/

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The de Rham complex `Ω^0_{B/A} → Ω^1_{B/A} → Ω^2_{B/A} → ⋯` of `B` over `A`: the exterior
powers of `Ω[B⁄A]`, as `A`-modules, with the de Rham differentials as its arrows.  The
construction has no hypothesis — the arrows are `deRhamDifferential` and the square-zero
condition is `deRhamDifferential_comp_deRhamDifferential`. -/
@[expose]
public noncomputable def deRhamComplex (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun p ↦ ModuleCat.of A ↥(⋀[B]^p (Ω[B⁄A])))
    (fun p ↦ ModuleCat.ofHom (deRhamDifferential (A := A) p))
    (fun p ↦ ModuleCat.hom_ext (deRhamDifferential_comp_deRhamDifferential p))

/-- The degree-`p` term of the de Rham complex is `Ω^p_{B/A} = ⋀[B]^p Ω[B⁄A]`. -/
@[simp] public theorem deRhamComplex_X (p : ℕ) :
    (deRhamComplex A B).X p = ModuleCat.of A ↥(⋀[B]^p (Ω[B⁄A])) := rfl

/-- The arrow of the de Rham complex out of degree `p` is `deRhamDifferential p`. -/
@[simp] public theorem deRhamComplex_d (p : ℕ) :
    (deRhamComplex A B).d p (p + 1) =
      ModuleCat.ofHom (deRhamDifferential (A := A) (B := B) p) := by
  apply CochainComplex.of_d

/-- The defining rule of the de Rham complex, read on its arrows:
`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`.  For `p = 0` this is the statement that
the degree-zero arrow is the universal derivation. -/
public theorem deRhamComplex_d_smul_ιMulti_D (p : ℕ) (b : Fin (p + 1) → B) :
    ((deRhamComplex A B).d p (p + 1)).hom
        (b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) =
      exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i) := by
  rw [deRhamComplex_d]
  exact deRhamDifferential_smul_ιMulti_D p b

/-- The defining rule determines the de Rham complex: a family of `A`-linear maps on the
exterior powers of `Ω[B⁄A]` obeying `d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ ⋯ ∧ d b_p` assembles
into `deRhamComplex A B`, whatever proof of the square-zero property it is supplied with. -/
public theorem deRhamComplex_unique
    (d' : ∀ p : ℕ, ⋀[B]^p (Ω[B⁄A]) →ₗ[A] ⋀[B]^(p + 1) (Ω[B⁄A]))
    (hd' : ∀ (p : ℕ) (b : Fin (p + 1) → B),
      d' p (b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) =
        exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i))
    (hsq : ∀ p : ℕ, ModuleCat.ofHom (d' p) ≫ ModuleCat.ofHom (d' (p + 1)) = 0) :
    CochainComplex.of (fun p ↦ ModuleCat.of A ↥(⋀[B]^p (Ω[B⁄A])))
        (fun p ↦ ModuleCat.ofHom (d' p)) hsq = deRhamComplex A B := by
  have hdd : d' = fun p ↦ deRhamDifferential (A := A) (B := B) p :=
    funext fun p ↦ deRhamDifferential_unique p (d' p) (hd' p)
  subst hdd
  rfl

end Complex

end KaehlerDifferential

end MathlibExt.DeRhamSource
