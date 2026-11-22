# Dyadic Lebesgue differentiation theorem for locally integrable functions

Let $F$ be a real Banach space and $f \colon \mathbb{R} \to F$ locally integrable. Then for almost every $x$,

$$\lim_{n \to \infty} \frac{1}{|I_n(x)|} \int_{I_n(x)} f(y)\, dy = f(x),$$

where $I_n(x)$ is the level-$n$ [dyadic interval](dyadic-interval.md) containing $x$. This is T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 5.1 (Lebesgue's differentiation theorem along cubes containing $x$ with side length tending to $0$), restricted to dyadic intervals in dimension one; the source allows all cubes containing $x$, so in that respect the statement is weaker, and it allows vector-valued $f$, which the source does not discuss. The averages are Bochner averages, which are genuine since $f$ is integrable on bounded intervals.

The proof applies Lebesgue's differentiation theorem for uniformly locally doubling measures to the closed intervals $[m 2^{-n}, (m+1) 2^{-n}]$ (closed balls of radius $2^{-n-1}$ containing $x$), which differ from the dyadic intervals by a null set.

## Informally uses

- [Dyadic interval](dyadic-interval.md): its agreement with a closed ball up to a null set.

## Background

- [Lebesgue differentiation along shrinking off-center intervals](../../../../Probability/stochastic-calculus/it-integral/ae-tendsto-average-icc.md): for real-valued $f$ that statement already contains the theorem, since $x \in I_n(x)$ lies within half the length of the midpoint of $I_n(x)$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
