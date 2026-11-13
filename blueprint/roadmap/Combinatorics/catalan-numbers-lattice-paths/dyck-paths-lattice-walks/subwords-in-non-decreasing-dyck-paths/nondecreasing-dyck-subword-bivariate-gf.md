# Bivariate generating function of a subword in non-decreasing Dyck paths

For a word $w$
in the steps $U$ and $D$, let $D_n$ be the set of non-decreasing Dyck paths of semilength $n$,
and let $\#w(P)$ be the number of occurrences of $w$ as a contiguous subword of a path $P$,
overlapping occurrences counted separately. The bivariate generating function $F_w(x, y)$ is
the power series in $x$ with coefficients in $\mathbb{Z}[y]$ given by

$$F_w(x, y) = \sum_{n \ge 1} \sum_{P \in D_n} y^{\#w(P)} x^n,$$

so its constant coefficient is $0$: the empty path is not counted.

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1.
