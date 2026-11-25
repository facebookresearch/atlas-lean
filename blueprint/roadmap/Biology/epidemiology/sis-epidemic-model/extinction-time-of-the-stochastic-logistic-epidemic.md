# Extinction time of the stochastic logistic SIS epidemic

This page covers a research target from Andersson and Djehiche (1998). In the stochastic SIS epidemic, the logistic epidemic, in a closed population of size $N$, let $T_N$ be the time until no one is infected, and let $R_0$ be the basic reproduction number of [the deterministic SIS model](deriv-infected-pos-iff.md). The target is the threshold limit theorem:

- if $R_0 > 1$, then, started from a quasi-endemic level, $T_N / \mathbb{E}[T_N]$ converges in distribution to the exponential law with mean $1$, and $\mathbb{E}[T_N]$ grows exponentially in $N$;
- if $R_0 < 1$, extinction occurs in a time of order $\log N$.

## Expansion

Fix from the source the initial condition, the exact growth rate of $\mathbb{E}[T_N]$ and the sense of the $\log N$ bound, state the two parts as theorems, and prove them.

Prerequisites:

- [Threshold theorem for the SIS model](deriv-infected-pos-iff.md)

## Sources

- H. Andersson and B. Djehiche, A threshold limit theorem for the stochastic logistic epidemic, *J. Appl. Probab.* 35 (1998), 662–670, <https://doi.org/10.1239/jap/1032265214>.
