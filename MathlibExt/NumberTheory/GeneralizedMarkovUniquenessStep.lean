/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree

/-!
# Children of generalized Cohn triples

This module publicly re-exports `MetaMathlibExt.IsGenCohnTriple.step`, proved in
`MathlibExt.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree` from the child
constructions used there to build generalized Cohn trees: both children of a generalized Cohn
triple are generalized Cohn triples over the Vieta jumpings of its generalized Markov triple.
It adds no declarations.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5.
-/
