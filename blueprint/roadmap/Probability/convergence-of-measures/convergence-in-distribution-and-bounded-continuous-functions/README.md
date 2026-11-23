# Convergence in distribution and bounded continuous functions

Real random variables $X_n$ converge in distribution to $X_\infty$, meaning that their distribution functions
converge at every continuity point of the limit, if and only if $E g(X_n) \to E g(X_\infty)$ for every bounded
continuous function $g \colon \mathbb R \to \mathbb R$.

## Idea

The second condition does not mention distribution functions, so it defines weak convergence of
probability measures on any topological space. The restriction to continuity points matters: if $X_n = 1/n$ and
$X_\infty = 0$, then $P(X_n \le 0) = 0$ for every $n$ while $P(X_\infty \le 0) = 1$, yet $X_n$ converges to $X_\infty$
in distribution, as $E g(X_n) = g(1/n) \to g(0)$ shows. One direction uses the Skorokhod representation and the bounded
convergence theorem; the other approximates the indicator of $(-\infty, x]$ by continuous piecewise linear
functions.

## Statements

- [Convergence in distribution through bounded continuous functions](weak-convergence-bounded-continuous.md)

## Background

- [Skorokhod representation on the real line](../skorokhod-representation-on-the-real-line/README.md): the Skorokhod representation used in the proof
- [Change of variables formula](../../foundations/laws-of-random-variables-and-identical-distribut/change-of-variables/README.md): expected values depend only on the distribution
