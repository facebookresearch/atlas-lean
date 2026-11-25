/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SymmetricGroupProductOrdersKourovka18Problem49

open MathlibExt.GroupTheory.SymmetricGroupProductOrdersKourovka18Problem49Wanted

-- The smallest degree allowed by the hypotheses.
example : ∃ x y : Equiv.Perm (Fin 4), orderOf x = 2 ∧ orderOf y = 2 ∧ orderOf (x * y) = 2 :=
  symmetricGroupHasProductWithOrders_holds 4 2 2 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Two odd factor orders with an even product order at the degree bound.
example : ∃ x y : Equiv.Perm (Fin 8), orderOf x = 3 ∧ orderOf y = 5 ∧ orderOf (x * y) = 6 :=
  symmetricGroupHasProductWithOrders_holds 8 3 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- An even factor whose order is one below the odd product order.
example : ∃ x y : Equiv.Perm (Fin 7), orderOf x = 4 ∧ orderOf y = 5 ∧ orderOf (x * y) = 5 :=
  symmetricGroupHasProductWithOrders_holds 7 4 5 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : ∃ x y : Equiv.Perm (Fin 6), orderOf x = 4 ∧ orderOf y = 4 ∧ orderOf (x * y) = 4 :=
  symmetricGroupHasProductWithOrders_holds 6 4 4 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The largest order belongs to the first factor.
example : ∃ x y : Equiv.Perm (Fin 33), orderOf x = 31 ∧ orderOf y = 2 ∧ orderOf (x * y) = 3 :=
  symmetricGroupHasProductWithOrders_holds 33 31 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
