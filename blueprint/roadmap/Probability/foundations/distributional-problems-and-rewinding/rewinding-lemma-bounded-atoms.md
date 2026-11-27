# Rewinding lemma for challenge laws with bounded atoms

Consider a two-stage experiment: a first stage outputs a state $s$; a challenge $t$ is drawn from a law $C(s)$ on a finite set; a second stage, using fresh randomness, answers $a$; the run succeeds if a test $\mathrm{ok}(s, t, a)$ passes. Let $\varepsilon$ be the one-run success probability, and let $\delta$ be the probability that two runs sharing the first-stage state $s$, with challenges $t, t'$ drawn independently from $C(s)$ and independent second-stage randomness, both succeed and have $t \ne t'$. If every atom of $C(s)$ has mass at most $\kappa$ for every possible state $s$, then

$$
\varepsilon^2 - \kappa\,\varepsilon \le \delta, \qquad\text{hence}\qquad \varepsilon \le \kappa + \sqrt{\delta}.
$$

For a uniform challenge among $N$ values ($\kappa = 1/N$) this is $\varepsilon^2 - \varepsilon/N \le \delta$. The atom bound must hold conditionally on each state; a bound on the unconditional challenge law does not suffice.

## Proof sketch

Fix $s$ and let $q(t) \in [0,1]$ be the second stage's success probability on challenge $t$, so the conditional one-run success is $e_s = \sum_t C(s)(t)q(t)$. The conditional two-run success with distinct challenges is $e_s^2 - \sum_t C(s)(t)^2 q(t)^2 \ge e_s^2 - \kappa e_s$, using $q^2 \le q$. Averaging over $s$ and Jensen's inequality $\mathbb{E}[e_s^2] \ge \varepsilon^2$ give the bound, and solving the quadratic gives $\varepsilon \le \kappa + \sqrt\delta$.

## Depends on

- [The rewinding lemma](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Proof depends on

- [The rewinding lemma](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
