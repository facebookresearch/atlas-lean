/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single.lean`
and
`P2M/Sol/S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single.lean`
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

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

@[expose] public section

namespace AddMonoidAlgebra

/-- A bialgebra endomorphism of an additive group algebra over a domain
sends each monomial `single g 1` to a monomial `single (M g) 1`, for an
additive monoid homomorphism `M` on the group.

The monomials are group-like, group-like elements of a group algebra over
a domain are exactly the monomials `single h 1`, and multiplicativity of
the bialgebra map then makes the assignment `g ↦ M g` additive. -/
public theorem exists_addMonoidHom_forall_bialgHom_single_eq_single
    {S : Type*} [CommRing S] [IsDomain S] (G : Type*) [AddCommGroup G]
    (f : AddMonoidAlgebra S G →ₐc[S] AddMonoidAlgebra S G) :
    ∃ M : G →+ G, ∀ g : G,
      f (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (M g) 1 :=
  ⟨mapDomainOfBialgHom f, fun g => (single_mapDomainOfBialgHom f g 1).symm⟩

end AddMonoidAlgebra
