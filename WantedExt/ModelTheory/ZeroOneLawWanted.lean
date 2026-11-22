/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.ModelTheory.LabelledStructureCount
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The zero-one law for first-order logic

For a finite relational vocabulary, every first-order sentence is either almost surely true
or almost surely false on labelled finite structures: the proportion of structures on
`{1, …, n}` satisfying it converges to `0` or to `1` (Glebskii, Kogan, Liogon'kii and Talanov
1969; Fagin 1976). The proportion is `FirstOrder.Language.satFraction`.

The hypotheses are those of the classical statement: no function or constant symbols
(`L.IsRelational`), finitely many relation symbols (`Finite L.Symbols`), and no relation
symbol of arity `0` (`IsEmpty (L.Relations 0)`). The last one is necessary: a nullary
relation symbol `P` is a propositional constant, true in exactly half of the structures on
every domain, so the sentence `P` has limiting proportion `1/2`.

## References

* Y. V. Glebskii, D. I. Kogan, M. I. Liogon'kii and V. A. Talanov, "Range and degree of
  realizability of formulas in the restricted predicate calculus", *Kibernetika* 2 (1969),
  17-28.
* R. Fagin, "Probabilities on finite models", *J. Symbolic Logic* 41 (1976), 50-58.
* P. G. Kolaitis and M. Y. Vardi, "0-1 laws for fragments of existential second-order logic:
  a survey", MFCS 2000, LNCS 1893, 84-98, Section 1 (statement of the law).
-/

@[expose] public section

namespace MathlibExt.ModelTheory.ZeroOneLawWanted

open FirstOrder FirstOrder.Language Filter Topology

/-- **Zero-one law for first-order logic.** Let `L` be a relational first-order language with
finitely many symbols and no nullary relation symbol. For every first-order sentence `φ`
(with equality) over `L`, the proportion of `L`-structures on `Fin n` in which `φ` holds
tends to `0` or to `1` as `n → ∞` (Glebskii, Kogan, Liogon'kii and Talanov, Kibernetika 1969;
Fagin, "Probabilities on finite models", J. Symbolic Logic 41, 1976; as stated in Kolaitis
and Vardi, "0-1 laws for fragments of existential second-order logic: a survey", MFCS 2000,
Section 1). -/
theorem_wanted zero_one_law (L : Language) [L.IsRelational] [IsEmpty (L.Relations 0)]
    [Finite L.Symbols] (φ : L.Sentence) :
    Tendsto (L.satFraction φ) atTop (𝓝 0) ∨ Tendsto (L.satFraction φ) atTop (𝓝 1)

end MathlibExt.ModelTheory.ZeroOneLawWanted
