# Vitali's theorem

There is a subset of $\mathbb{R}$ that is not Lebesgue measurable.

## Idea

Choose, with the axiom of choice, one point of $[0, 1]$ in each coset of the rationals, and call the
resulting set $V$. Its translates $V + q$ by the rationals $q \in [-1, 1]$ are pairwise disjoint,
cover $[0, 1]$ and lie in $[-1, 2]$. If $V$ were measurable with measure $c$, countable additivity
and translation invariance would give $1 \le \sum_q c \le 3$, which no value of $c$ satisfies. So
Lebesgue measure cannot be extended to all subsets of $\mathbb{R}$ as a countably additive,
translation-invariant measure.

## Statements

- [Vitali's theorem](vitali-nonmeasurable.md)

## Background

- [Lebesgue measurability by approximation](../../lebesgue-measure/lebesgue-measurability/README.md): the notion of measurability that the Vitali set escapes.

## Sources

- G. Vitali, *Sul problema della misura dei gruppi di punti di una retta*, Tipografia Gamberini e Parmeggiani, Bologna, 1905.
