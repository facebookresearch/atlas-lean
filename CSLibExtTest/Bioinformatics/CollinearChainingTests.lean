/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.CollinearChaining

/-! # Regressions for weighted collinear chaining -/

set_option autoImplicit false

namespace Cslib.Bioinformatics.CollinearChaining.Tests

private def a : Anchor := ⟨1, 1, 10⟩
private def b : Anchor := ⟨2, 4, 7⟩
private def c : Anchor := ⟨3, 5, 6⟩

-- The second rank determines the larger gap. The best chain uses both extensions.
example : (scoreTable 3 (-2) [c, b, a]).ret = [(c, 19), (b, 13), (a, 10)] := by
  decide

-- The first extension is rejected when its gap is exactly the limit.
example : (scoreTable 2 (-2) [c, b, a]).ret = [(c, 13), (b, 7), (a, 10)] := by
  decide

-- Even an admissible extension can lose to starting a new chain.
example : (scoreTable 3 (-10) [c, b, a]).ret = [(c, 13), (b, 7), (a, 10)] := by
  decide

private def tied : Anchor := ⟨2, 2, 100⟩
private def crossed : Anchor := ⟨1, 9, 100⟩

-- Neither a tied first rank nor a decreasing second rank allows an extension into `b`.
example : (scoreTable 100 0 [b, tied, crossed]).ret = [(b, 7), (tied, 100), (crossed, 100)] := by
  decide

-- A gap of 2 on the first axis and 1 on the second costs 4, not 2 or 6.
private def firstDominant : Anchor := ⟨4, 3, 7⟩

example : (scoreTable 3 (-2) [firstDominant, a]).ret = [(firstDominant, 13), (a, 10)] := by
  decide

-- A smaller first rank does not allow an extension when the second ranks tie.
private def tiedSecond : Anchor := ⟨1, 4, 100⟩

example : (scoreTable 100 0 [b, tiedSecond]).ret = [(b, 7), (tiedSecond, 100)] := by
  decide

-- The cost counts all inspected table entries, even for rejected pairs.
example : (scoreTable 0 (-2) [c, b, a]).time = 3 := by
  decide

end Cslib.Bioinformatics.CollinearChaining.Tests
