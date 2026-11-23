/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoSubdivisionComposition

/-!
# The admissible-mono subdivision functor to Quillen Q

The selected quotient of an admissible monomorphism and the quotient span
attached to a subdivision square form a functor to the Quillen
Q-construction.  Identity and composition are supplied by the separately
proved span-coherence theorems.

This file makes no nerve, realization, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The functor sending an admissible mono to its selected quotient and a
Segal-subdivision factorization to its quotient-level Quillen span. -/
@[simps]
noncomputable def admissibleMonoSubdivisionQuillenFunctor :
    AdmissibleMonoSubdivision (C := C) ⥤ QuillenQ C where
  obj := admissibleMonoSubdivisionQuillenObj
  map := admissibleMonoSubdivisionQuillenHom
  map_id := admissibleMonoSubdivisionQuillenHom_id
  map_comp := fun f g ↦
    (admissibleMonoSubdivisionQuillenHom_comp f g).symm

end AlgebraicKTheory

end
