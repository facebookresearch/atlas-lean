# Star commutes with a commuting test

In any [Kleene algebra with tests](kleene-algebras-with-tests.md), if $bq = qb$ for a test $b$ and an element $q$, then

$$b q^\ast = (bq)^\ast b = q^\ast b = b (qb)^\ast .$$

The equation $bq^\ast = (bq)^\ast$ fails in general: for $b = 0$ the left side is $0$ and the right side is $1$.

## Depends on

- [Kleene algebras with tests](kleene-algebras-with-tests.md)

## Proof depends on

- [A one-step simulation lifts to finite iteration](../../kleene-algebra-with-tests/star-simulation.md)

## Sources

- D. Kozen, "Kleene algebra with tests", *ACM Transactions on Programming Languages and Systems* 19(3):427–443, 1997, author copy <https://www.cs.cornell.edu/~kozen/Papers/kat.pdf>, Section 2.3, Lemma 2.3.2 and the remark after it.
