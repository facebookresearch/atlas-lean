# End components

Let $M = (S, \bar s, \alpha_M, \delta_M, L)$ be a [Markov decision process](markov-decision-processes-and-adversaries.md). An *end component* (EC) of $M$ is a pair $(S', \delta')$ of a set $S' \subseteq S$ of states and a partial probabilistic transition function $\delta' : S' \times \alpha_M \to \mathrm{Dist}(S)$ such that

- $(S', \delta')$ is a sub-MDP of $M$: for all $s' \in S'$ and $a \in \alpha_M$, if $\delta'(s', a)$ is defined then $\delta'(s', a) = \delta_M(s', a)$ and $\delta'(s', a)(s'') > 0$ only for states $s'' \in S'$;
- the underlying graph of $(S', \delta')$ is strongly connected.

An EC $(S', \delta')$ is *maximal* if there is no distinct EC $(S'', \delta'')$ such that $\delta''(s, a)$ is defined whenever $\delta'(s, a)$ is. Intuitively, an end component is a set of states of the MDP in which it is possible to remain forever once entered.

## Depends on

- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 3, Definition 6.
