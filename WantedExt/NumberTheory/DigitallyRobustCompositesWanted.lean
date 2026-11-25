/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.DigitallyRobustComposites

namespace MetaMathlibExt

/--
**Infinitely many digitally robust composites.** There are infinitely many natural numbers that
are digitally robust composites: composite numbers coprime to $10$ that stay composite after
replacing any one base-ten digit (including a leading zero) by a different digit, after deleting
any one of their digits, and after inserting any digit in any position.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem_wanted infinitelyMany_digitallyRobustComposites :
    {N : ℕ | IsDigitallyRobustComposite N}.Infinite

end MetaMathlibExt
