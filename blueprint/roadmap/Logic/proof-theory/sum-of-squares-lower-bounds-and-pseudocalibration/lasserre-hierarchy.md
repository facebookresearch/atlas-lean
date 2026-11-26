# The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization

Let $p, q_1, \dots, q_m \in \mathbb{R}[x_1, \dots, x_n]$ and consider maximizing $p(x)$ over $x \in \{0,1\}^n$ subject to $q_j(x) = 0$. The **degree-$d$ sum-of-squares (Lasserre) relaxation** is the semidefinite program

$$
\mathrm{SoS}_d = \max\Bigl\{\, \tilde{\mathbb{E}}[p] \;:\; \tilde{\mathbb{E}} : \mathbb{R}[x]_{\le d} \to \mathbb{R} \text{ linear},\ \tilde{\mathbb{E}}[1] = 1,\ \tilde{\mathbb{E}}[(x_i^2 - x_i) r] = 0,\ \tilde{\mathbb{E}}[q_j r] = 0,\ \tilde{\mathbb{E}}[s^2] \ge 0 \,\Bigr\},
$$

over all polynomials $r$ and $s$ of degrees making the arguments have degree at most $d$. Its value is at least the true maximum, decreases with $d$, equals it at $d = 2n$, and can be computed to additive precision $\eta$ in time $n^{O(d)} \operatorname{polylog}(1/\eta)$ under bit-complexity conditions. By duality, $\mathrm{SoS}_d \le c$ certifies $p \le c$ on the feasible Boolean points via a degree-$d$ sum-of-squares identity.

## Depends on

- [Pebble games with counting and the Sherali–Adams hierarchy](../../../TheoryOfComputation/descriptive-complexity/pebble-games-with-counting.md)
- [Objective of the MAX CUT semidefinite program](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/sdp-objective.md)

## Sources

- J. B. Lasserre, "Global optimization with polynomials and the problem of moments", SIAM Journal on Optimization 11 (2001) 796-817.
- P. A. Parrilo, "Structured semidefinite programs and semialgebraic geometry methods in robustness and optimization", PhD thesis, Caltech (2000).
- N. Fleming, P. Kothari, T. Pitassi, "Semialgebraic proofs and efficient algorithm design", Foundations and Trends in Theoretical Computer Science 14 (2019).
