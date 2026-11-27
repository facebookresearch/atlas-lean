# Function-space MCMC

Markov chain Monte Carlo for posteriors with density $\exp(-\Phi)$ against a Gaussian prior $N(0, C)$, designed to make sense on function space so that its performance does not degrade under mesh refinement. A proposal reversible for the prior turns Metropolis–Hastings into an accept–reject step on differences of the potential alone, $a(u, v) = \min\{1, \exp(\Phi(u) - \Phi(v))\}$. The preconditioned Crank–Nicolson (pCN) proposal $v = \sqrt{1 - \beta^2}\, u + \beta \xi$, $\xi \sim N(0, C)$, is such a proposal.

- [The pCN proposal map](pcn-proposal.md)
- [Continuity of the pCN proposal map](continuous-pcn-proposal.md)
- [Measurability of the pCN proposal map](measurable-pcn-proposal.md)
- [The pCN proposal kernel](pcn-kernel.md)
- [Evaluation of the pCN kernel](pcn-kernel-apply.md)
- [The joint law of a pCN step is symmetric](map-swap-pcn-eq.md)
- [Prior reversibility of the pCN proposal](is-reversible-pcn-kernel.md)
- [The pCN proposal preserves its Gaussian prior](invariant-pcn-kernel.md)
- [Detailed balance makes the joint law symmetric](map-swap-comp-prod-eq-of-is-reversible.md)
- [Metropolis–Hastings acceptance probability for a prior-reversible proposal](mh-accept-potential.md)
- [Measurability of the acceptance probability](measurable-mh-accept-potential.md)
- [The acceptance probability is at most one](mh-accept-potential-le-one.md)
- [Metropolis–Hastings kernel for a prior-reversible proposal](mh-kernel.md)
- [Evaluation of the Metropolis–Hastings kernel](mh-kernel-apply.md)
- [The Metropolis–Hastings kernel is a Markov kernel](is-markov-kernel-mh-kernel.md)
- [Metropolis–Hastings with a prior-reversible proposal is reversible for the posterior](is-reversible-mh-kernel.md)
- [The posterior is invariant for Metropolis–Hastings with a prior-reversible proposal](invariant-mh-kernel.md)
- [The pCN method is reversible for the posterior](is-reversible-pcn-mh-kernel.md)

## Related topics

- [Markov chain Monte Carlo](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/README.md): Metropolis–Hastings and Gibbs sampling on a finite state space, with general proposals.
- [Ornstein–Uhlenbeck process](../../stochastic-calculus/ornstein-uhlenbeck-process/README.md): the pCN proposal is a Crank–Nicolson discretisation of the Ornstein–Uhlenbeck dynamics $du = -u\,ds + \sqrt{2C}\,db$, which leaves the Gaussian prior invariant (Cotter, Roberts, Stuart and White, equations (4.2) and (4.7)).
- [Mixing times of Markov chains](../../markov-chains/mixing-times-of-markov-chains/README.md): reversibility gives invariance of the posterior; mixing times measure how fast the chain gets there.
- [Canonical paths and multicommodity flow](../../markov-chains/canonical-paths-and-multicommodity-flow/README.md): spectral-gap bounds for reversible chains.
- [Bayesian inverse problems](../bayesian-inverse-problems/README.md): the posteriors these chains sample.
