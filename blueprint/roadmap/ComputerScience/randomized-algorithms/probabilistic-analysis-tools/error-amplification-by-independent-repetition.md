# Error amplification by independent repetition

Let $A$ be a randomized algorithm for a decision problem. If $A$ has one-sided error of RP type (it never accepts a no-instance and rejects a yes-instance with probability at most $\delta < 1$), then accepting when at least one of $k$ independent runs accepts gives error at most $\delta^k$; dually for coRP-type error, accepting when all $k$ runs accept gives error at most $\delta^k$. If $A$ errs with probability at most $1/2 - \varepsilon$ on every input, then the majority vote of $k$ independent runs errs with probability at most $e^{-2\varepsilon^2 k}$ by Hoeffding's inequality. A Las Vegas algorithm with expected running time $T$, stopped after $2T$ steps, finishes with probability at least $1/2$ by Markov's inequality.

## Depends on

- [Las Vegas and Monte Carlo algorithms](las-vegas-and-monte-carlo-algorithms.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- A. Gupta, *Advanced Algorithms*, lecture notes for CMU 15-850, Fall 2020, <https://www.cs.cmu.edu/~15850/notes/cmu850-f20.pdf>
- M. Mitzenmacher and E. Upfal, *Probability and Computing*, 2nd ed., Cambridge University Press, 2017
