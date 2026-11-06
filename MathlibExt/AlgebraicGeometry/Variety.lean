/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Varieties over a field

A *variety* over a field `k` is a scheme `X` equipped with a structure morphism to
`Spec k` that is separated, of finite type, and geometrically reduced.

We follow the "geometric" convention (see Görtz–Wedhorn, *Algebraic Geometry I*, and the
Stacks project morphism-property tags): the structure morphism `X ⟶ Spec k` is
* separated (`AlgebraicGeometry.IsSeparated`, Stacks tag `01KM`),
* of finite type, i.e. quasi-compact and locally of finite type
  (`AlgebraicGeometry.QuasiCompact` + `AlgebraicGeometry.LocallyOfFiniteType`, Stacks tag `01T0`),
* geometrically reduced (`AlgebraicGeometry.GeometricallyReduced`, Stacks tag `0364`).

Requiring geometric (rather than plain) reducedness makes the notion stable under base
change / field extension, which is why it is the "geometric" convention.

## Main definitions

* `AlgebraicGeometry.IsVariety`: the predicate on a `k`-scheme of being a variety over `k`.

## Implementation notes

`IsVariety` is a `Prop`-valued `class` on `AlgebraicGeometry.Scheme` whose separatedness,
finite-type, and geometric-reducedness hypotheses are stated explicitly on the structure
morphism `X ↘ Spec (CommRingCat.of k)` (obtained from the `X.Over (Spec (CommRingCat.of k))`
instance). It is built by composing existing Mathlib morphism properties rather than
introducing any new primitive.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- **Variety over a field.** Let $k$ be a field. A scheme $X$ with a chosen structure morphism
$X \to \operatorname{Spec} k$ is a *variety* over $k$ if this morphism is separated, of finite
type (quasi-compact and locally of finite type), and geometrically reduced. -/
class IsVariety (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] : Prop where
  /-- The structure morphism `X ⟶ Spec k` is separated. -/
  isSeparated : IsSeparated (X ↘ Spec (CommRingCat.of k))
  /-- The structure morphism `X ⟶ Spec k` is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))
  /-- The structure morphism `X ⟶ Spec k` is quasi-compact. -/
  quasiCompact : QuasiCompact (X ↘ Spec (CommRingCat.of k))
  /-- The structure morphism `X ⟶ Spec k` is geometrically reduced. -/
  geometricallyReduced : GeometricallyReduced (X ↘ Spec (CommRingCat.of k))

namespace IsVariety

variable {k}
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

instance [IsVariety k X] : IsSeparated (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.isSeparated

instance [IsVariety k X] : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.locallyOfFiniteType

instance [IsVariety k X] : QuasiCompact (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.quasiCompact

instance [IsVariety k X] : GeometricallyReduced (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.geometricallyReduced

variable (k X) in
/-- **Characterization of varieties.** Let $k$ be a field and let $X$ be a scheme with a
structure morphism $X \to \operatorname{Spec} k$. Then $X$ is a variety over $k$ if and only if
this structure morphism is separated, locally of finite type, quasi-compact and geometrically
reduced. -/
theorem isVariety_iff :
    IsVariety k X ↔
      IsSeparated (X ↘ Spec (CommRingCat.of k)) ∧
        LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) ∧
          QuasiCompact (X ↘ Spec (CommRingCat.of k)) ∧
            GeometricallyReduced (X ↘ Spec (CommRingCat.of k)) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- **Varieties are quasi-separated.** If $X$ is a variety over a field $k$, then its structure
morphism $X \to \operatorname{Spec} k$ is quasi-separated, since it is separated. -/
theorem quasiSeparated [IsVariety k X] :
    QuasiSeparated (X ↘ Spec (CommRingCat.of k)) :=
  inferInstance

end IsVariety

section Examples

/-- Affine space `𝔸ⁿ_k` over a field `k` is a variety over `k`. -/
example (n : Type u) [Finite n] : IsVariety k (𝔸(n; Spec (CommRingCat.of k))) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Boundary case: the zero-dimensional affine space `𝔸⁰_k` (a single `k`-rational point)
is a variety over `k`. -/
example : IsVariety k (𝔸(PEmpty.{u + 1}; Spec (CommRingCat.of k))) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end Examples

end AlgebraicGeometry

end
