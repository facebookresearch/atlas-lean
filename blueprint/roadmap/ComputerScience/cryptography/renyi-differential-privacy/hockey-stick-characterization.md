# Differential privacy as a hockey-stick divergence bound

For distributions $P, Q$ on a countable set and $\gamma \ge 1$, the *hockey-stick divergence* is $E_\gamma(P \Vert Q) = \sup_S \bigl(P(S) - \gamma Q(S)\bigr) = \sum_r \max(0, P(r) - \gamma Q(r))$. A mechanism $M$ is $(\varepsilon, \delta)$-differentially private with respect to an adjacency relation if and only if $E_{e^\varepsilon}(M(x) \Vert M(y)) \le \delta$ for all adjacent $x, y$. In particular pure $(\varepsilon, 0)$-differential privacy is the pointwise likelihood-ratio bound $M(x)(r) \le e^\varepsilon M(y)(r)$ for all outputs $r$.

## Proof sketch

The supremum over events is attained at $S = \{r : P(r) > \gamma Q(r)\}$.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
- Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan, "Universally Utility-Maximizing Privacy Mechanisms", SIAM Journal on Computing, 2012.
