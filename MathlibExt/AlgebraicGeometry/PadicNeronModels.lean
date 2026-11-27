/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import MathlibExt.AlgebraicGeometry.NeronModels

/-!
# Néron models over the p-adic integers

The base is `Spec ℤ_p`, with its fraction-field inclusion and residue-field
quotient to `𝔽_p = ZMod p`. Generic and special fibres are scheme pullbacks.
A Néron model over `ℤ_p` is the general finite-type Néron model of
`NeronModels` for `ℤ_p ⊂ ℚ_p`, with its Hom equivalence and extension maps.
Only the identification of the residue field with `ZMod p`, used to reduce
integral points to `𝔽_p`-points, is specific to this file. Existence of
models of abelian varieties is the general request of `NeronModelsWanted`.

Reference: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §§1.1–1.3.
https://doi.org/10.1007/978-3-642-51438-8
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PadicNeronModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- The actual complete discrete valuation trait. -/
abbrev trait : Scheme.{0} := SemistableModels.trait (PadicInt p)

/-- Its fraction-field point. -/
abbrev genericBase : Scheme.{0} := Spec (CommRingCat.of.{0} (Padic p))

/-- Its residue-field point. -/
abbrev specialBase : Scheme.{0} := Spec (CommRingCat.of.{0} (ZMod p))

/-- The actual inclusion of the fraction field. -/
abbrev genericInclusion : genericBase p ⟶ trait p :=
  SemistableModels.genericInclusion (PadicInt p) (Padic p)

/-- The actual quotient to the residue field `ZMod p`. -/
def specialInclusion : specialBase p ⟶ trait p :=
  Spec.map (CommRingCat.ofHom (PadicInt.toZMod))

/-- The scheme-theoretic generic-fibre functor. -/
abbrev genericFunctor : Over (trait p) ⥤ Over (genericBase p) :=
  SemistableModels.genericFunctor (PadicInt p) (Padic p)

/-- The scheme-theoretic special-fibre functor. -/
abbrev specialFunctor : Over (trait p) ⥤ Over (specialBase p) :=
  Over.pullback (specialInclusion p)

/-- A finite-type Néron model over `ℤ_p` of a scheme `A` over `ℚ_p`: the general
`NeronModels.FiniteTypeNeronModel` for `ℤ_p ⊂ ℚ_p`. -/
abbrev NeronModel (A : Over (genericBase p)) :=
  NeronModels.FiniteTypeNeronModel (PadicInt p) (Padic p) A

/-- Integral scheme-valued points over `ℤ_p`. -/
abbrev IntegralPoint (N : Over (trait p)) := NeronModels.IntegralPoint (PadicInt p) N

/-- Points of the actual special fibre over the residue field. -/
abbrev SpecialPoint (N : Over (trait p)) :=
  {q : specialBase p ⟶ ((specialFunctor p).obj N).left //
    q ≫ ((specialFunctor p).obj N).hom = 𝟙 _}

/-- Reduction is induced by the actual residue quotient and pullback square. -/
def reducePoint (N : Over (trait p)) (q : IntegralPoint p N) :
    SpecialPoint p N :=
  ⟨pullback.lift (specialInclusion p ≫ q.1) (𝟙 _) (by
      simp [Category.assoc, q.2]),
    pullback.lift_snd _ _ _⟩

end MathlibExt.AlgebraicGeometry.PadicNeronModels
