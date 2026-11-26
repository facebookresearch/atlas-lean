# Maximum probability of an omega-regular property

Let $M = (S, \bar s, \alpha_M, \delta_M)$ be a [Markov decision process](markov-decision-processes-and-adversaries.md) and $A = (Q, \bar q, \alpha_M, \delta_A, \{(L_i, K_i)\}_{i=1}^k)$ a [deterministic Rabin automaton](deterministic-rabin-automata.md). The product $M \otimes A$ is the MDP with states $S \times Q$, initial state $(\bar s, \bar q)$ and $\delta((s, q), a) = \delta_M(s, a) \times [\delta_A(q, a) \mapsto 1]$ for $a \in A(s)$, undefined otherwise. An [end component](end-components.md) $(S', \delta')$ of $M \otimes A$ is *accepting* if for some $i$ the projection of $S'$ onto $Q$ contains a state of $K_i$ and no state of $L_i$. Then for every state $s$,

$$\Pr^{\max}_{M,s}(\{\pi \mid \mathrm{tr}(\pi) \in L(A)\}) = \Pr^{\max}_{M \otimes A, (s, \bar q)}(\mathit{reach}(T)),$$

where $\mathrm{tr}(\pi)$ is the action trace of $\pi$ as on [regular safety properties](regular-safety-properties.md), and $T$ is the set of states $(s', q')$ that belong to some accepting end component of $M \otimes A$. This reduces LTL and $\omega$-regular model checking of MDPs to end-component detection and maximum reachability.

## Depends on

- [Regular safety properties](regular-safety-properties.md)
- [Deterministic Rabin automata](deterministic-rabin-automata.md)
- [End components](end-components.md)
- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 7.3, Definition 22, the correspondence of adversaries between $M$ and $M \otimes A$, and Proposition 2.
