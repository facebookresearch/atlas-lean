# Reward structures

A *reward structure* for a [Markov decision process](markov-decision-processes-and-adversaries.md) $M = (S, \bar s, \alpha_M, \delta_M, L)$ is a pair $r = (r_{\mathrm{state}}, r_{\mathrm{action}})$ of a state reward function $r_{\mathrm{state}} : S \to \mathbb{R}_{\ge 0}$ and an action reward function $r_{\mathrm{action}} : S \times \alpha_M \to \mathbb{R}_{\ge 0}$. Rewards often model costs such as energy consumption or the number of lost requests; action rewards are also called transition, impulse or state-action rewards.

## Depends on

- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 3, Definition 5.
