# Zero-one law for first-order logic

Let $L$ be a first-order language with no function or constant symbols, finitely many relation
symbols, and no relation symbol of arity $0$. For every first-order sentence $\varphi$ over $L$
(with equality), the proportion $\mu_n(\varphi)$ of $L$-structures on $\{1, \dots, n\}$ that
satisfy $\varphi$ converges, and its limit is $0$ or $1$.

The hypothesis that no relation
symbol is nullary is part of the classical setting and is necessary: a nullary symbol $P$ is a
propositional constant, true in exactly half of the structures on every domain, so
$\mu_n(P) = 1/2$ for all $n$.

The classical proof considers the extension axioms: for each pair of finite configurations, the
sentence saying that every copy of the smaller one extends to a copy of the larger one. Each
extension axiom has probability tending to $1$; the theory they axiomatize has no finite models
and is $\aleph_0$-categorical (its countable model is the random structure), hence complete; so
every sentence or its negation follows from finitely many extension axioms, and has probability
tending to $1$. The same argument decides the limit, in contrast with Trakhtenbrot's theorem
that validity on all finite structures is undecidable as soon as the vocabulary has a binary
relation symbol. The law fails for existential
second-order logic, since the parity of the domain size is definable there.

## Informally uses

- [Proportion for a negated sentence](sat-fraction-not.md): a limit $0$ for $\varphi$ is a limit
  $1$ for $\neg\varphi$.

## Background

- [Proportion of labelled structures satisfying a sentence](sat-fraction.md): the quantity
  whose limit is taken.
- [Gödel's completeness theorem](../../first-order-logic/g-del-s-completeness-theorem/README.md):
  the compactness argument behind the completeness of the theory of extension axioms.
- [Fagin's theorem](../../../TheoryOfComputation/descriptive-complexity/fagin-s-theorem/README.md):
  existential second-order logic captures NP, and has no zero-one law.

## Sources

- Y. V. Glebskii, D. I. Kogan, M. I. Liogon'kii and V. A. Talanov, "Range and degree of realizability of formulas in the restricted predicate calculus", *Kibernetika* 2 (1969), 17-28.
- R. Fagin, "Probabilities on finite models", *J. Symbolic Logic* 41 (1976), 50-58.
- P. G. Kolaitis and M. Y. Vardi, "0-1 laws for fragments of existential second-order logic: a survey", MFCS 2000, LNCS 1893, Springer 2000, pp. 84-98, Section 1 (author's posted version, https://www.cs.rice.edu/~vardi/papers/mfcs00i.pdf).
