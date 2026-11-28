/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_ProjSpace.lean` and
`Theorems/Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean` and
`P2M/Sol/S_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the definitions, statement and proof are reused here with that
machinery removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjSpace.Segre

/-!
# Chow data over a base ring

For a scheme `V` over `Spec R`, a `ChowDatum` is a proper morphism `V' ⟶ V`
that is an isomorphism over a dense open of `V`, together with a closed
immersion of `V'` over `Spec R` into a finite fibre product of projective
spaces. A `ChowDatumProj` is the same with a single projective space as
target. Composing with the iterated Segre embedding turns the first into the
second (`AlgebraicGeometry.ChowDatumProj.nonempty_of`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

/-- A Chow datum for `π : V ⟶ Spec R`: a proper modification `p : V' ⟶ V`,
an isomorphism over the dense open `U`, together with a closed immersion of
`V'` over `Spec R` into a finite fibre product of projective spaces. -/
structure ChowDatum where
  /-- The number of projective factors. -/
  m : ℕ
  /-- The dimensions of the projective factors. -/
  e : Fin m → ℕ
  /-- The source of the modification. -/
  V' : Scheme.{u}
  /-- The modification. -/
  p : V' ⟶ V
  /-- The embedding into the product of projective spaces. -/
  ι : V' ⟶ ProjSpace.prodOver R e
  /-- The modification is proper. -/
  hp_proper : IsProper p
  /-- The embedding is a closed immersion. -/
  hι_closed : IsClosedImmersion ι
  /-- The embedding lies over `Spec R`. -/
  hover : ι ≫ ProjSpace.prodOverπ R e = p ≫ π
  /-- The open over which the modification is an isomorphism. -/
  U : V.Opens
  /-- That open is dense. -/
  hU_dense : Dense (U : Set V)
  /-- The modification is an isomorphism over `U`. -/
  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatum.hp_proper ChowDatum.hι_closed ChowDatum.hp_isoU

/-- A Chow datum for `π : V ⟶ Spec R` whose embedding lands in a single
projective space over `Spec R`. -/
structure ChowDatumProj where
  /-- The dimension of the target projective space. -/
  Nd : ℕ
  /-- The source of the modification. -/
  V' : Scheme.{u}
  /-- The modification. -/
  p : V' ⟶ V
  /-- The embedding into projective space. -/
  ιN : V' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)
  /-- The modification is proper. -/
  hp_proper : IsProper p
  /-- The embedding is a closed immersion. -/
  hιN_closed : IsClosedImmersion ιN
  /-- The embedding lies over `Spec R`. -/
  hoverN : ιN ≫ ProjSpace.π R Nd = p ≫ π
  /-- The open over which the modification is an isomorphism. -/
  U : V.Opens
  /-- That open is dense. -/
  hU_dense : Dense (U : Set V)
  /-- The modification is an isomorphism over `U`. -/
  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatumProj.hp_proper ChowDatumProj.hιN_closed
  ChowDatumProj.hp_isoU

open ProjSpace.Segre in
/-- A Chow datum into a product of projective spaces gives one into a single
projective space, by composing with the iterated Segre embedding. -/
def ChowDatum.toChowDatumProj (D : ChowDatum π) : ChowDatumProj π where
  Nd := (segreAux R D.e).Nd
  V' := D.V'
  p := D.p
  ιN := D.ι ≫ (segreAux R D.e).segσ
  hp_proper := D.hp_proper
  hιN_closed := by
    have := (segreAux R D.e).hσ_closed
    infer_instance
  hoverN := by
    rw [Category.assoc, (segreAux R D.e).hσ_over, D.hover]
  U := D.U
  hU_dense := D.hU_dense
  hp_isoU := D.hp_isoU

/-- If `π : V ⟶ Spec R` admits a Chow datum into a finite product of
projective spaces, it admits one into a single projective space. -/
theorem ChowDatumProj.nonempty_of :
    Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) :=
  fun ⟨D⟩ => ⟨D.toChowDatumProj π⟩

end AlgebraicGeometry
