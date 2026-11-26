# The second fixed point theorem

Fix a recursive enumeration $n \mapsto t_n$ of the untyped λ-terms up to α-equivalence and write $[\![t]\!]$ for the Church numeral $\underline{n} = \lambda f x.\, f^n x$ of the
index $n$ with $t_n = t$ (the *code* of $t$). For every term $F$ there is a term $A$ with

$$A \simeq_\beta F\, [\![A]\!].$$

So a term may refer to its own code: for a term $\Phi$ with a free variable $x$, taking $F = \lambda x.\, \Phi$ gives a term $A$ with $A \simeq_\beta \Phi[[\![A]\!]/x]$.

## Proof depends on

- [λ-definable functions are exactly the partial recursive functions](../../../TheoryOfComputation/equivalence-of-models/counter-and-combinator-models/lambda-definable-functions-are-exactly-the.md)

## Expansion

This page becomes ready once:

- Untyped λ-terms up to α-equivalence with one-step β-reduction, β-conversion $\simeq_\beta$ and the Church–Rosser theorem (statement prerequisite; not yet stated as a page)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 2, Section 4, Theorem 2.19 and the remark that follows it.
