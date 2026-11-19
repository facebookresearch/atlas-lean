/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.ExpenditureDuality

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.BudgetSetCollision

section BothOpen

open _root_.Economics.Consumer MathlibExt.Economics.Consumer

/-- With both consumer namespaces open, unqualified `budgetSet` is unambiguous:
it resolves to the `MathlibExt` copy. -/
example : @budgetSet = @MathlibExt.Economics.Consumer.budgetSet := rfl

/-- `Economics.Consumer.budgetSet` is an alias of the canonical `MathlibExt` copy, not a
second definition: the two qualified names resolve to the same constant, so the
previously public name keeps compiling. -/
example : @Economics.Consumer.budgetSet =
    @MathlibExt.Economics.Consumer.budgetSet := rfl

/-- Importing only duality does not expose the separate two-good demand API. -/
example : @IsMarshallianDemand = @_root_.Economics.Consumer.IsMarshallianDemand := rfl

end BothOpen

end MathlibExtTest.Economics.Consumer.BudgetSetCollision
