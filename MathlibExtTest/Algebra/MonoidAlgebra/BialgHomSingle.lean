/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MonoidAlgebra.BialgHomSingle

@[expose] public section

universe u v

/-- Consumer with the original binders, in universe `0`. -/
theorem exactSource
    {S : Type} [CommRing S] [IsDomain S] (G : Type) [AddCommGroup G]
    (f : AddMonoidAlgebra S G →ₐc[S] AddMonoidAlgebra S G) :
    ∃ M : G →+ G, ∀ g : G,
      f (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (M g) 1 :=
  AddMonoidAlgebra.exists_addMonoidHom_forall_bialgHom_single_eq_single G f

/-- Higher-universe consumer: the coefficient ring and the group may live
in independent universes. -/
example
    {S : Type u} [CommRing S] [IsDomain S] (G : Type v) [AddCommGroup G]
    (f : AddMonoidAlgebra S G →ₐc[S] AddMonoidAlgebra S G) :
    ∃ M : G →+ G, ∀ g : G,
      f (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (M g) 1 :=
  AddMonoidAlgebra.exists_addMonoidHom_forall_bialgHom_single_eq_single G f

/-- The identity bialgebra map is induced by the identity homomorphism. -/
example (G : Type*) [AddCommGroup G] :
    ∃ M : G →+ G, ∀ g : G,
      (BialgHom.id ℤ (AddMonoidAlgebra ℤ G)) (AddMonoidAlgebra.single g 1) =
        AddMonoidAlgebra.single (M g) 1 :=
  AddMonoidAlgebra.exists_addMonoidHom_forall_bialgHom_single_eq_single G
    (BialgHom.id ℤ (AddMonoidAlgebra ℤ G))
