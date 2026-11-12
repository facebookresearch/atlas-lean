/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import MathlibExt.Economics.Consumer.ExpenditureDuality

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.BudgetSetCollision

section BothOpen

open _root_.Economics.Consumer MathlibExt.Economics.Consumer

/-- With both consumer namespaces open, unqualified `budgetSet` is unambiguous:
it resolves to the `MathlibExt` copy. -/
example : @budgetSet = @MathlibExt.Economics.Consumer.budgetSet := rfl

/-- With both consumer namespaces open, `consumerBudgetSet` is the duality-API
copy in `Economics.Consumer`. -/
example : @consumerBudgetSet = @_root_.Economics.Consumer.consumerBudgetSet := rfl

/-- The two budget sets are definitionally the same set-builder. -/
example : @MathlibExt.Economics.Consumer.budgetSet =
    @_root_.Economics.Consumer.consumerBudgetSet := rfl

end BothOpen

end MathlibExtTest.Economics.Consumer.BudgetSetCollision
