# Markov decision processes and adversaries

A *Markov decision process* (MDP) is a tuple $M = (S, \bar s, \alpha, \delta, L)$ of a finite set $S$ of states, an initial state $\bar s$, a finite alphabet $\alpha$ of actions, a partial probabilistic transition function $\delta : S \times \alpha \to \mathrm{Dist}(S)$ and a labelling $L : S \to 2^{AP}$. The set $A(s)$ of actions $a$ for which $\delta(s, a)$ is defined is assumed nonempty for every $s$. A step from $s$ first chooses an action $a \in A(s)$ nondeterministically and then a successor $s'$ with probability $\delta(s, a)(s')$. An infinite path is a sequence $s_0 a_0 s_1 a_1 \cdots$ with $a_i \in A(s_i)$ and $\delta(s_i, a_i)(s_{i+1}) > 0$; finite paths are its prefixes ending in a state.

An *adversary* is a function $\sigma$ from finite paths to distributions on actions with $\sigma(\rho)(a) > 0$ only for $a \in A(\mathrm{last}(\rho))$. It is *deterministic* if every $\sigma(\rho)$ is a point distribution and *memoryless* if $\sigma(\rho)$ depends only on $\mathrm{last}(\rho)$. An adversary $\sigma$ induces a [DTMC](discrete-time-markov-chains.md) $M^\sigma$ whose states are the finite paths of $M$, with transition probability $\sigma(\rho)(a) \cdot \delta(\mathrm{last}(\rho), a)(s)$ from $\rho$ to $\rho a s$; its path measure gives the probability measure $\Pr^\sigma_{M,s}$ on the infinite paths of $M$ from $s$. For a memoryless adversary the induced chain can be taken finite. This labelled, adversary-based notion differs from the [Markov decision process with rewards](../../../ComputerScience/heuristic-search-and-planning/value-iteration/mdp.md) of dynamic programming, which has a reward for each state and action but no labelling and no adversaries.

## Depends on

- [Discrete-time Markov chains](discrete-time-markov-chains.md)

## Related topics

- [Markov decision process](../../../ComputerScience/heuristic-search-and-planning/value-iteration/mdp.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 3, Definitions 4, 7, 8 and 10 and the discussion of quotient chains after Definition 11.
