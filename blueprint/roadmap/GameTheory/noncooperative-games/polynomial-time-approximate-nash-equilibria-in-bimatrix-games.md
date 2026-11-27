# Polynomial-time approximate Nash equilibria in bimatrix games

For two-player games with payoffs in [0, 1], what is the smallest constant ε for which an ε-approximate Nash equilibrium, in which no player gains more than ε by a unilateral deviation, can be computed in polynomial time?

## What would settle it

Give a polynomial-time algorithm achieving a smaller constant, or prove a hardness result showing that some constant is a barrier. A polynomial-time algorithm for every fixed ε > 0 would contradict the exponential-time hypothesis for PPAD by the result recorded below. Exact equilibrium existence does not give an efficient approximation algorithm.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status.

Li and Li (preprint) give a polynomial-time algorithm with guarantee below 1/3 and call the smallest error achievable in polynomial time a fundamental open question. They record Rubinstein's result that, under the exponential-time hypothesis for PPAD, quasi-polynomial time is necessary for sufficiently small constant errors.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Dongchen Li and Hanyu Li, *A Simple Algorithm Breaking the 1/3 Barrier for Approximate Nash Equilibria in Bimatrix Games*, arXiv:2610.05317v1 (2026), §1. <https://arxiv.org/abs/2610.05317v1>
