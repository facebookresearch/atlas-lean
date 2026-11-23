/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Nerve.SegalSubdivision
public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoTripleSpanTarget
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Quillen spans from the Segal subdivision of admissible monomorphisms

Let `iP` be the wide subcategory of admissible monomorphisms in an exact
category `P`.  An object of `SegalSubdivision iP` is an admissible mono
`A ↪ B`; its selected Q-object is the quotient `B/A`.

A subdivision morphism is a factorization

```text
A' ↪ A ↪ B ↪ B'.
```

The admissible-mono triple construction gives a raw span from `B/A` to the
selected quotient of the composite.  The subdivision factorization equation
identifies that composite with `A' ↪ B'`, so the equality-invariance of the
selected quotient transports the span to `B'/A'`.

This file constructs the object assignment, raw span, and quotient-level
Quillen morphism.  Identity, composition, the bundled functor, nerve, and
realization claims remain separate.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The wide subcategory of admissible monomorphisms. -/
abbrev AdmissibleMonoCategory :=
  WideSubcategory (admissibleMonosOf C IsAdmissibleExact)

/-- Segal subdivision of the admissible-monomorphism category. -/
abbrev AdmissibleMonoSubdivision :=
  SegalSubdivision (AdmissibleMonoCategory (C := C))

/-- Selected quotient object represented by an admissible mono in the Segal
subdivision. -/
noncomputable abbrev admissibleMonoSubdivisionQuotient
    (x : AdmissibleMonoSubdivision (C := C)) : C :=
  AdmissibleMonoFlag.admissibleMonoQuotient x.val.hom x.val.property

/-- Object of the Quillen Q-construction selected by a subdivision object. -/
noncomputable def admissibleMonoSubdivisionQuillenObj
    (x : AdmissibleMonoSubdivision (C := C)) : QuillenQ C :=
  ⟨admissibleMonoSubdivisionQuotient x⟩

/-- Underlying factorization equation of a morphism in the Segal
subdivision of admissible monomorphisms. -/
theorem admissibleMonoSubdivisionHom_factorization
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    ((w.hom.1.unop).hom ≫ x.val.hom) ≫ w.hom.2.hom =
      y.val.hom := by
  have hw := w.map_val
  change w.hom.1.unop ≫ x.val ≫ w.hom.2 = y.val at hw
  simpa only [WideSubcategory.comp_def, Category.assoc] using
    congrArg InducedWideCategory.Hom.hom hw

/-- Raw Quillen span attached to a Segal-subdivision morphism. -/
noncomputable def admissibleMonoSubdivisionQuillenSpan
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    QuillenSpan (admissibleMonoSubdivisionQuotient x)
      (admissibleMonoSubdivisionQuotient y) := by
  let a := w.hom.1.unop
  let b := w.hom.2
  let hcomp :=
    AdmissibleMonoFlag.admissibleMonoTriple_comp_admissible
      a.hom a.property x.val.hom x.val.property b.hom b.property
  let S := AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
    a.hom a.property x.val.hom x.val.property b.hom b.property
  let eTarget := AdmissibleMonoFlag.admissibleMonoQuotientIsoOfEq
    hcomp y.val.property
      (admissibleMonoSubdivisionHom_factorization w)
  exact QuillenSpan.endpointTransport S (Iso.refl _) eTarget

/-- Quotient-level Quillen morphism attached to a Segal-subdivision
morphism. -/
noncomputable def admissibleMonoSubdivisionQuillenHom
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    admissibleMonoSubdivisionQuillenObj x ⟶
      admissibleMonoSubdivisionQuillenObj y :=
  QuillenQ.mkHom (admissibleMonoSubdivisionQuillenSpan w)

end AlgebraicKTheory

end
