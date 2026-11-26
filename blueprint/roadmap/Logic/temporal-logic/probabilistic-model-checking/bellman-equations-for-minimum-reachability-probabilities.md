# Bellman equations for minimum reachability probabilities

Let $M$ be a finite [Markov decision process](markov-decision-processes-and-adversaries.md) with target set $T$. The values $x_s = \Pr^{\min}_s(\mathit{reach}(T))$ form the unique solution of the equations

$$x_s = 1 \text{ if } s \in S^1_{\min}, \qquad x_s = 0 \text{ if } s \in S^0_{\min}, \qquad x_s = \min_{a \in A(s)} \sum_{s' \in S} \delta(s, a)(s')\, x_{s'} \text{ otherwise},$$

with the [qualitative sets](qualitative-reachability-by-graph-analysis.md) $S^0_{\min}$ and $S^1_{\min}$; the equations remain uniquely solvable when $S^1_{\min}$ is replaced by $T$. The proof views minimum reachability as a stochastic shortest path problem.

## Depends on

- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Proof depends on

- [Qualitative reachability by graph analysis](qualitative-reachability-by-graph-analysis.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 4.2 (Bellman equations for minimum probabilities).
