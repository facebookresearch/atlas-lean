# Probabilistic safety reduces to reachability in a product

Let $M = (S, \bar s, \alpha_M, \delta_M, L_M)$ be a [Markov decision process](markov-decision-processes-and-adversaries.md) and $\Phi_P$ a [regular safety property](regular-safety-properties.md) with $\alpha_P \subseteq \alpha_M$ and error automaton $A^{\mathrm{err}}_P = (Q, \bar q, \alpha_P, \delta_P, F)$. The *product* $M \otimes A^{\mathrm{err}}_P$ is the MDP with states $S \times Q$, initial state $(\bar s, \bar q)$, actions $\alpha_M$ and

$$\delta((s, q), a) = \begin{cases} \delta_M(s, a) \times [\delta_P(q, a) \mapsto 1] & \text{if } a \in A(s) \cap \alpha_P, \\ \delta_M(s, a) \times [q \mapsto 1] & \text{if } a \in A(s) \setminus \alpha_P, \\ \text{undefined} & \text{otherwise,} \end{cases}$$

with the labelling of $s$, extended by a proposition $\mathit{err}_P$ when $q \in F$. Then for every state $s$,

$$\Pr^{\min}_{M,s}(\Phi_P) = 1 - \Pr^{\max}_{M \otimes A^{\mathrm{err}}_P, (s, \bar q)}(\mathit{reach}(S \times F)).$$

## Depends on

- [Regular safety properties](regular-safety-properties.md)
- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 7.1, Definition 17 and Proposition 1.
