# Value iteration converges to extremal reachability probabilities

Let $M$ be a finite [Markov decision process](markov-decision-processes-and-adversaries.md) with target set $T$ and [qualitative sets](qualitative-reachability-by-graph-analysis.md) $S^0_{\min}$, $S^1_{\min}$. Define $x^n_s$ for $n \in \mathbb{N}$ by $x^n_s = 1$ for $s \in S^1_{\min}$, $x^n_s = 0$ for $s \in S^0_{\min}$, $x^0_s = 0$ for all other $s$, and

$$x^n_s = \min_{a \in A(s)} \sum_{s' \in S} \delta(s, a)(s')\, x^{n-1}_{s'} \qquad (n \ge 1)$$

for all other $s$. Then $\lim_{n \to \infty} x^n_s = \Pr^{\min}_s(\mathit{reach}(T))$ for every state $s$, and the same holds for $\Pr^{\max}_s(\mathit{reach}(T))$ with $\max$ in place of $\min$ and the sets $S^0_{\max}$, $S^1_{\max}$. The usual stopping criterion, a small difference between successive iterates, does not guarantee that the result is within that tolerance of the limit.

## Depends on

- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Proof depends on

- [Qualitative reachability by graph analysis](qualitative-reachability-by-graph-analysis.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 4.2 (value iteration and Algorithm 5).
