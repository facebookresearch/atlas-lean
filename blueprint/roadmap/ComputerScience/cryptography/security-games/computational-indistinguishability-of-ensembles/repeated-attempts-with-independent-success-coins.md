# Repeated simulation attempts with independent success coins

Let $\mu$ be a distribution on outputs and let $p \in [0,1]$. Suppose each attempt of a procedure independently succeeds with probability $p$, and conditioned on success its output has law $\mu$. Running $k$ attempts and returning the output of the first successful one (or a fixed fallback $d$ if all fail) produces a distribution $\nu_k$ with

$$\Delta(\nu_k, \mu) \le (1 - p)^k.$$

In particular, a simulator that guesses a verifier's challenge from a set of size $m$ (so $p = 1/m$) and rewinds $k = n m$ times is within statistical distance $e^{-n}$ of the honest view.

## Proof sketch

Conditioned on at least one success the output is exactly $\mu$, by independence of the success coins from the outputs; all failures happen with probability $(1-p)^k$, and on that event the distance is at most $1$.

## Depends on

- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- S. Goldwasser, S. Micali and C. Rackoff, "The Knowledge Complexity of Interactive Proof Systems", SIAM Journal on Computing 18(1), 1989.
